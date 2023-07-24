// Types

type var = string;
let string_of_var = (x: var): string => x;

type typ =
  | Base
  | Hole
  | Fun(typ, typ);
let rec string_of_typ = (t: typ): string => {
  switch (t) {
  | Base => "B"
  | Hole => "?"
  | Fun(t1, t2) =>
    "(" ++ string_of_typ(t1) ++ " -> " ++ string_of_typ(t2) ++ ")"
  };
};

type typ_conflict_report = {
  t1: typ,
  t2: typ,
  t1_min: typ,
  t2_min: typ,
};
let string_of_typ_conflict_report =
    ({t1, t2, t1_min, t2_min}: typ_conflict_report): string => {
  let minimized_elaboration =
    if (t1 == t1_min && t2 == t2_min) {
      "";
    } else {
      " (because "
      ++ string_of_typ(t1_min)
      ++ " can't match "
      ++ string_of_typ(t2_min)
      ++ ")";
    };
  string_of_typ(t1)
  ++ " can't match "
  ++ string_of_typ(t2)
  ++ minimized_elaboration
  ++ ".";
};

type merge_result =
  | Success(typ)
  | Fail(typ_conflict_report);

type exp =
  | Var(var)
  | Fun(var, exp)
  | App(exp, exp)
  | Asc(exp, typ);
let rec string_of_exp = (e: exp): string => {
  switch (e) {
  | Var(x) => string_of_var(x)
  | Asc(Fun(x, e), Fun(t1, t2)) =>
    "(fun "
    ++ string_of_exp(Asc(Var(x), t1))
    ++ " -> "
    ++ string_of_exp(Asc(e, t2))
    ++ ")"
  | Fun(x, e) =>
    "(fun " ++ string_of_var(x) ++ " -> " ++ string_of_exp(e) ++ ")"
  | App(e1, e2) => string_of_exp(e1) ++ "(" ++ string_of_exp(e2) ++ ")"
  | Asc(e, t) => string_of_exp(e) ++ ":" ++ string_of_typ(t)
  };
};

// type expected_typ_report =
//   | Nil;
// type context_item_report =
//   | Abs(expected_typ_report)
//   | Var({
//       context_item_report,
//       expected_typ_report,
//     });

type context =
  | Nil
  | Cons((var, typ), context);
let rec string_of_context = (gamma: context): string => {
  switch (gamma) {
  | Nil => "."
  | Cons((x, t), Nil) => string_of_var(x) ++ ": " ++ string_of_typ(t)
  | Cons((x, t), gamma) =>
    string_of_context(Cons((x, t), Nil))
    ++ ", "
    ++ string_of_context(gamma)
  };
};

type error_report =
  // | Var_Absent({location: exp})
  | Var_Present({
      location: exp,
      context_typ: typ,
      expected_typ: typ,
      typ_conflict_report,
    });
// | Asc({
//     location: exp,
//     asc_typ: typ,
//     expected_typ: typ,
//     typ_conflict_report,
//   })
// | Fun({
//     location: exp,
//     expected_typ: typ,
//   });

let string_of_error_report = (report: error_report): string =>
  switch (report) {
  | Var_Present({location, context_typ, expected_typ, typ_conflict_report}) =>
    string_of_exp(location)
    ++ " seems to have type "
    ++ string_of_typ(context_typ)
    ++ " but needs to have type "
    ++ string_of_typ(expected_typ)
    ++ ". "
    ++ string_of_typ_conflict_report(typ_conflict_report)
  // | _ => "TODO"
  };

// Functions

let rec merge = (t1: typ, t2: typ): merge_result => {
  switch (t1, t2) {
  | (Base, Base) => Success(Base)
  | (Hole, t2) => Success(t2)
  | (t1, Hole) => Success(t1)
  | (Fun(t3, t4), Fun(t5, t6)) =>
    switch (merge(t3, t5), merge(t4, t6)) {
    | (Success(t7), Success(t8)) => Success(Fun(t7, t8))
    | (Fail(report), _) => Fail({...report, t1, t2})
    | (_, Fail(report)) => Fail({...report, t1, t2})
    }
  | (Base, Fun(_, _))
  | (Fun(_, _), Base) => Fail({t1, t2, t1_min: t1, t2_min: t2})
  };
};
let match_arrow = (t: typ): (typ, typ) => {
  switch (t) {
  | Fun(t1, t2) => (t1, t2)
  | Hole => (Hole, Hole)
  | Base => failwith("no")
  };
};

let rec item_in_context = (item, gamma): bool => {
  switch (gamma) {
  | Nil => false
  | Cons(item2, _) when item2 == item => true
  | Cons(_, gamma2) => item_in_context(item, gamma2)
  };
};

let rec context_in_context = (gamma1: context, gamma2: context): bool => {
  switch (gamma1, gamma2) {
  | (Nil, _) => true
  | (Cons(item, gamma3), gamma2) =>
    if (item_in_context(item, gamma2)) {
      context_in_context(gamma3, gamma2);
    } else {
      false;
    }
  };
};

let context_equal = (gamma1, gamma2) =>
  context_in_context(gamma1, gamma2) && context_in_context(gamma2, gamma1);

let rec context_add = (gamma: context, x: var, t: typ): context => {
  switch (gamma) {
  | Nil => Cons((x, t), Nil)
  | Cons((y, _), gamma2) when x == y => Cons((x, t), gamma2)
  | Cons(pair, gamma2) => Cons(pair, context_add(gamma2, x, t))
  };
};
let rec context_search = (gamma: context, x: var): typ => {
  switch (gamma) {
  | Nil => Hole
  | Cons((y, t), _) when x == y => t
  | Cons(_, gamma2) => context_search(gamma2, x)
  };
};
let rec context_remove = (gamma: context, x: var): context => {
  switch (gamma) {
  | Nil => Nil
  | Cons((y, _), gamma2) when x == y => gamma2
  | Cons(pair, gamma2) => Cons(pair, context_remove(gamma2, x))
  };
};
let rec context_merge_item = (gamma: context, x: var, t: typ): context => {
  switch (gamma) {
  | Nil => Cons((x, t), Nil)
  | Cons((y, t2), gamma2) when x == y =>
    switch (merge(t, t2)) {
    | Success(t3) => Cons((x, t3), gamma2)
    | Fail(report) =>
      print_endline(string_of_typ_conflict_report(report));
      failwith("error");
    }
  | Cons(pair, gamma2) => Cons(pair, context_merge_item(gamma2, x, t))
  };
};
let rec context_merge = (gamma1: context, gamma2: context): context => {
  switch (gamma1) {
  | Nil => gamma2
  | Cons((x, t), gamma3) =>
    context_merge(gamma3, context_merge_item(gamma2, x, t))
  };
};

// Main process function

let rec process = (e: exp, t: typ, gamma: context): (typ, context) => {
  // print_endline(
  //   string_of_context(gamma)
  //   ++ " |- "
  //   ++ string_of_typ(t)
  //   ++ " => "
  //   ++ string_of_exp(e),
  // );
  let return = (return_t: typ, return_gamma: context): (typ, context) => {
    (
      // print_endline(
      //   string_of_context(gamma)
      //   ++ " |- "
      //   ++ string_of_typ(t)
      //   ++ " => "
      //   ++ string_of_exp(e)
      //   ++ " => "
      //   ++ string_of_typ(return_t)
      //   ++ " -| "
      //   ++ string_of_context(return_gamma),
      // );
      return_t,
      return_gamma,
    );
  };
  switch (e) {
  | Var(x) => process_var(x, t, gamma, return)
  | Fun(x, e) => process_fun(x, e, t, gamma, return)
  | App(e1, e2) => process_app(e1, e2, t, gamma, return)
  | Asc(e, t2) => process_asc(e, t2, t, gamma, return)
  };
}
and process_var = (x, t, gamma, return) => {
  let context_t = context_search(gamma, x);
  switch (merge(context_t, t)) {
  | Success(t2) => return(t2, context_add(gamma, x, t2))
  | Fail(typ_conflict_report) =>
    let error_report =
      Var_Present({
        location: Var(x),
        context_typ: context_t,
        expected_typ: t,
        typ_conflict_report,
      });
    print_endline(string_of_error_report(error_report));
    failwith("error");
  };
}
and process_fun = (x, e, t, gamma, return) => {
  let (t1, t2) = match_arrow(t);
  let (t3, gamma2) = process(e, t2, context_add(gamma, x, t1));
  return(
    Fun(context_search(gamma2, x), t3): typ,
    context_remove(gamma2, x),
  );
}
and process_app = (e1, e2, t, gamma, return) => {
  let app_helper =
      (t_in: typ, t_out: typ, gamma: context): (typ, typ, context) => {
    let (t2, gamma_intermediate) = process(e1, Fun(t_in, t_out), gamma);
    let (t_in_intermediate, t_out_new) = match_arrow(t2);

    let (t_in_new, gamma_new) =
      process(e2, t_in_intermediate, gamma_intermediate);
    (t_in_new, t_out_new, context_merge(gamma_intermediate, gamma_new));
  };
  let rec app_loop = (t_in: typ, t_out: typ, gamma: context) => {
    let (t_in_new, t_out_new, gamma_new) = app_helper(t_in, t_out, gamma);
    if (t_in_new == t_in
        && t_out_new == t_out
        && context_equal(gamma_new, gamma)) {
      return(t_out_new, gamma_new);
    } else {
      app_loop(t_in_new, t_out_new, gamma_new);
    };
  };
  app_loop(Hole, t, gamma);
}
and process_asc = (e, t2, t, gamma, return) => {
  switch (merge(t, t2)) {
  | Success(t3) =>
    let (return_t, return_gamma) = process(e, t3, gamma);
    return(return_t, return_gamma);
  | Fail(report) =>
    print_endline(string_of_typ_conflict_report(report));
    failwith("error");
  };
};

// Testing

let test = (e: exp) => {
  print_endline(string_of_exp(e));
  let (t, gamma) = process(e, Hole, Nil);
  print_endline(string_of_typ(t));
  print_endline(string_of_context(gamma));
};

let let_exp = (x: var, e1: exp, e2: exp): exp => App(Fun(x, e2), e1);
let const = (x: var, t: typ, e: exp): exp => Asc(Fun(x, e), Fun(t, Hole));

// This first example tests the case that I brought up. If you look up in the
// trace you can see it infers the types of a, b, and c to be B -> B.
let example_term_long =
  const(
    "+",
    Fun(Base, Fun(Base, Base)),
    const(
      "0",
      Base,
      App(
        App(
          Var("+"),
          App(
            Var("a"),
            App(
              Var("b"),
              App(
                Var("c"),
                App(Var("d"), App(Var("e"), App(Var("f"), Var("0")))),
              ),
            ),
          ),
        ),
        App(
          Var("f"),
          App(
            Var("e"),
            App(
              Var("d"),
              App(Var("c"), App(Var("b"), App(Var("a"), Var("0")))),
            ),
          ),
        ),
      ),
    ),
  );
test(example_term_long);

// This tests the one kind of error I currently have implemented: a constructur
// mismatch when unifying context type and analyzed type of a var
let failure_example_term =
  const(
    "+",
    Fun(Base, Fun(Base, Base)),
    const("0", Base, let_exp("a", Var("0"), App(Var("a"), Var("0")))),
  );
test(failure_example_term);

// let t1: typ = Fun(Fun(Fun(Hole, Base), Hole), Base);
// let t2: typ = Fun(Fun(Base, Hole), Base);

// switch (merge(t1, t2)) {
// | Success(_) => print_endline("impossible")
// | Fail(report) => print_endline(string_of_typ_conflict_report(report))
// };

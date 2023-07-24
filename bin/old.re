type option('a) =
  // | Some('a)
  | None;

// Types

type var = string;
let string_of_var = (x: var): string => x;

type typ =
  | Base
  | Hole
  | Fun(typ, typ);
type exp =
  | Var(var)
  | Fun(var, exp)
  | App(exp, exp)
  | Asc(exp, typ);

type location = unit;
type ana_report =
  | AnaHole
  // At location, typ => exp because [(_ -> typ) => (fun _ -> exp)]
  | AnaFun({
      location,
      exp,
      typ,
      ana_report,
    })
  // At location, (t_in -> t_out) => e1 because [t_out' => e1(e2)], [e2 => t_in'], and [e1 => (_ -> t_out'')]
  | AnaApp1({
      location,
      e1: exp,
      e2: exp,
      t_in: typ,
      t_out: typ,
      ana_report,
      arg_syn_report: option(syn_report),
      fun_syn_report: option(syn_report),
    })
  // At location (e1(e2)), (t_in => e2) because [e1 => (t_in' -> _)] and [e2 => t_in'']
  | AnaApp2({
      location,
      e1: exp,
      e2: exp,
      typ,
      arg_syn_report: option(syn_report),
      fun_syn_report: option(syn_report),
    })
  // At location, (exp : t => typ) because [t' => e]
  | AnaAsc({
      location,
      exp,
      typ,
      t_annotated: typ,
      t_expected: typ,
      ana_report,
    })
and syn_report =
  // At location, var => typ because [gamma |- var : gamma(var)] combined with [t => var].
  | SynVar({
      location,
      var,
      typ,
      context_report,
      ana_report,
    })
  // At location, (fun var -> exp) => (t1 -> t2) because [gamma' |- var : t1] and exp => t2
  | SynFun({
      location,
      var,
      exp,
      t1: typ,
      t2: typ,
      context_report,
      syn_report,
    })
  // At location, e1(e2) => typ because [e1 => (_ -> typ)]
  | SynApp({
      location,
      e1: exp,
      e2: exp,
      typ,
      syn_report,
    })
  // At location, (exp : _) => typ because [exp => typ]
  | SynAsc({
      location,
      exp,
      typ,
      syn_report,
    })
and context_report =
  | ConAbsent
  // At location, [gamma |- var : typ] because [t1 => var] combined with [gamma |- var : gamma(var)]
  | ConVar({
      location,
      var,
      typ,
      ana_report,
      context_report,
    })
  // At location, [gamma |- var : typ] because [(typ -> _) => fun var -> _]
  | ConFun({
      location,
      var,
      typ,
      ana_report,
    })
  | ConMerge({
      var,
      typ,
      context_report1: context_report,
      context_report2: context_report,
    });

type context =
  | Nil
  | Cons((var, typ, context_report), context);

type merge_report = {
  t1: typ,
  t2: typ,
  t1_min: typ,
  t2_min: typ,
};
type error_report =
  // | Var_Absent({location: exp})
  | Var_Present({
      location: exp,
      context_typ: typ,
      expected_typ: typ,
      merge_report,
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

let rec string_of_typ = (t: typ): string => {
  switch (t) {
  | Base => "B"
  | Hole => "?"
  | Fun(t1, t2) =>
    "(" ++ string_of_typ(t1) ++ " -> " ++ string_of_typ(t2) ++ ")"
  };
};
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
let rec string_of_context = (gamma: context): string => {
  switch (gamma) {
  | Nil => "."
  | Cons((x, t, _), Nil) => string_of_var(x) ++ ": " ++ string_of_typ(t)
  | Cons((x, t, report), gamma) =>
    string_of_context(Cons((x, t, report), Nil))
    ++ ", "
    ++ string_of_context(gamma)
  };
};
let rec string_of_ana_report_indent =
        (report: ana_report, indent: int): string => {
  let rec whitespace = n => {
    switch (n) {
    | 0 => ""
    | _ => "  " ++ whitespace(n - 1)
    };
  };
  whitespace(indent)
  ++ (
    switch (report) {
    | AnaHole => "[explain] for lack of information"
    | AnaFun(record) =>
      let e_string = string_of_exp(record.exp);
      let t_string = string_of_typ(record.typ);
      Printf.sprintf(
        "[explain] %s : %s because fun(... -> %s) : (... -> %s) \n%s",
        e_string,
        t_string,
        e_string,
        t_string,
        string_of_ana_report_indent(record.ana_report, indent + 1),
      );
    | AnaApp1(_) => "[ana app1]"
    | AnaApp2(_) => "[ana app2]"
    | AnaAsc(record) =>
      Printf.sprintf(
        "[explain] %s : %s by ascription",
        string_of_exp(record.exp),
        string_of_typ(record.typ),
      )
    }
  );
};
let string_of_ana_report = (report: ana_report): string => {
  string_of_ana_report_indent(report, 0);
};

let rec string_of_context_report_indent =
        (report: context_report, indent: int): string => {
  let rec whitespace = n => {
    switch (n) {
    | 0 => ""
    | _ => "  " ++ whitespace(n - 1)
    };
  };
  whitespace(indent)
  ++ (
    switch (report) {
    | ConAbsent => "[explain] for lack of information"
    | ConVar({location, var, typ, ana_report, context_report}) =>
      let _ = location;
      Printf.sprintf(
        "[explain] %s : %s because of a combination of: \n%s\n%s",
        string_of_var(var),
        string_of_typ(typ),
        string_of_ana_report_indent(ana_report, indent + 1),
        string_of_context_report_indent(context_report, indent + 1),
      );
    | ConFun({location, var, typ, ana_report}) =>
      let _ = location;
      Printf.sprintf(
        "[explain] %s : %s because fun %s -> _ : (%s -> _)\n%s",
        string_of_var(var),
        string_of_typ(typ),
        string_of_var(var),
        string_of_typ(typ),
        string_of_ana_report_indent(ana_report, indent + 1),
      );
    | ConMerge({var, typ, context_report1, context_report2}) =>
      print_endline("pse");
      let _ = context_report2;
      Printf.sprintf(
        "[explain] %s : %s because of a combination of: \n%s\n%s",
        string_of_var(var),
        string_of_typ(typ),
        string_of_context_report_indent(context_report1, indent + 1),
        "weird recursion",
        //string_of_context_report_indent(context_report2, indent + 1),
      );
    }
  );
};

let string_of_context_report = report =>
  string_of_context_report_indent(report, 0);

// Functions

let string_of_merge_report = ({t1, t2, t1_min, t2_min}: merge_report): string => {
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
  | Fail(merge_report);

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
  let (a, b, _) = item;
  switch (gamma) {
  | Nil => false
  | Cons((a', b', _), _) when a == a' && b == b' => true
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

let rec context_add =
        (gamma: context, x: var, t: typ, report: context_report): context => {
  switch (gamma) {
  | Nil => Cons((x, t, report), Nil)
  | Cons((y, _, _), gamma2) when x == y => Cons((x, t, report), gamma2)
  | Cons(item, gamma2) => Cons(item, context_add(gamma2, x, t, report))
  };
};
let rec context_search = (gamma: context, x: var): (typ, context_report) => {
  switch (gamma) {
  | Nil => (Hole, ConAbsent)
  | Cons((y, t, report), _) when x == y => (t, report)
  | Cons(_, gamma2) => context_search(gamma2, x)
  };
};
let rec context_remove = (gamma: context, x: var): context => {
  switch (gamma) {
  | Nil => Nil
  | Cons((y, _, _), gamma2) when x == y => gamma2
  | Cons(item, gamma2) => Cons(item, context_remove(gamma2, x))
  };
};
let rec context_merge_item =
        (gamma: context, x: var, t: typ, report: context_report): context => {
  switch (gamma) {
  | Nil => Cons((x, t, report), Nil)
  | Cons((y, t2, report2), gamma2) when x == y =>
    switch (merge(t, t2)) {
    | Success(t3) =>
      let merged_report =
        ConMerge({
          var: x,
          typ: t3,
          context_report1: report,
          context_report2: report2,
        });
      Cons((x, t3, merged_report), gamma2);
    | Fail(merge_report) =>
      print_endline(string_of_merge_report(merge_report));
      failwith("error");
    }
  | Cons(item, gamma2) =>
    Cons(item, context_merge_item(gamma2, x, t, report))
  };
};
let rec context_merge = (gamma1: context, gamma2: context): context => {
  switch (gamma1) {
  | Nil => gamma2
  | Cons((x, t, report), gamma3) =>
    context_merge(gamma3, context_merge_item(gamma2, x, t, report))
  };
};

let string_of_error_report = (report: error_report): string =>
  switch (report) {
  | Var_Present({location, context_typ, expected_typ, merge_report}) =>
    string_of_exp(location)
    ++ " seems to have type "
    ++ string_of_typ(context_typ)
    ++ " but needs to have type "
    ++ string_of_typ(expected_typ)
    ++ ". "
    ++ string_of_merge_report(merge_report)
  // | _ => "TODO"
  };

// Main process function

let rec process =
        (e: exp, t: typ, gamma: context, ana_report)
        : (typ, context, syn_report) => {
  switch (ana_report) {
  | AnaFun(_) =>
    print_endline(
      string_of_context(gamma)
      ++ " |- "
      ++ string_of_typ(t)
      ++ " => "
      ++ string_of_exp(e)
      ++ "\n"
      ++ string_of_ana_report(ana_report),
    )
  | _ => ()
  };
  let return =
      (return_t: typ, return_gamma: context, syn_report)
      : (typ, context, syn_report) => {
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
      syn_report,
    );
  };
  switch (e) {
  | Var(x) => process_var(x, t, gamma, ana_report, return)
  | Fun(x, e) => process_fun(x, e, t, gamma, ana_report, return)
  | App(e1, e2) => process_app(e1, e2, t, gamma, ana_report, return)
  | Asc(e, t2) => process_asc(e, t2, t, gamma, ana_report, return)
  };
}
and process_var = (x, t, gamma, ana_report, return) => {
  let (context_t, context_report) = context_search(gamma, x);
  switch (merge(context_t, t)) {
  | Success(t2) =>
    let context_report =
      ConVar({location: (), var: x, typ: t2, ana_report, context_report});
    let syn_report =
      SynVar({location: (), var: x, typ: t2, context_report, ana_report});
    return(t2, context_add(gamma, x, t2, context_report), syn_report);
  | Fail(merge_report) =>
    let error_report =
      Var_Present({
        location: Var(x),
        context_typ: context_t,
        expected_typ: t,
        merge_report,
      });
    failwith(string_of_error_report(error_report));
  };
}
and process_fun = (x, e, t, gamma, ana_report, return) => {
  let (t1, t2) = match_arrow(t);
  let ana_report_new = AnaFun({location: (), exp: e, typ: t, ana_report});
  let context_report_new =
    ConFun({location: (), var: x, typ: t1, ana_report});
  let (t3, gamma2, syn_report) =
    process(
      e,
      t2,
      context_add(gamma, x, t1, context_report_new),
      ana_report_new,
    );
  let (gamma_x, context_report) = context_search(gamma2, x);
  let syn_report_new =
    SynFun({
      location: (),
      var: x,
      exp: e,
      t1,
      t2,
      context_report,
      syn_report,
    });
  return(Fun(gamma_x, t3): typ, context_remove(gamma2, x), syn_report_new);
}
and process_app = (e1, e2, t, gamma, ana_report, return) => {
  let app_helper =
      (t_in: typ, t_out: typ, gamma: context, ana_report)
      : (typ, typ, context, syn_report) => {
    let ana_report1 =
      AnaApp1({
        location: (),
        e1,
        e2,
        t_in,
        t_out,
        ana_report,
        arg_syn_report: None,
        fun_syn_report: None,
      });
    let (t2, gamma_intermediate, syn_report1) =
      process(e1, Fun(t_in, t_out), gamma, ana_report1);
    let (t_in_intermediate, t_out_new) = match_arrow(t2);

    let ana_report2 =
      AnaApp2({
        location: (),
        e1,
        e2,
        typ: t_in_intermediate,
        arg_syn_report: None,
        fun_syn_report: None,
      });
    let (t_in_new, gamma_new, syn_report2) =
      process(e2, t_in_intermediate, gamma_intermediate, ana_report2);
    let syn_report =
      SynApp({location: (), e1, e2, typ: t_out_new, syn_report: syn_report1});
    let _ = syn_report2;
    (
      t_in_new,
      t_out_new,
      context_merge(gamma_intermediate, gamma_new),
      syn_report,
    );
  };
  let rec app_loop = (t_in: typ, t_out: typ, gamma: context, ana_report) => {
    let (t_in_new, t_out_new, gamma_new, syn_report_new) =
      app_helper(t_in, t_out, gamma, ana_report);
    if (t_in_new == t_in
        && t_out_new == t_out
        && context_equal(gamma_new, gamma)) {
      return(t_out_new, gamma_new, syn_report_new);
    } else {
      app_loop(t_in_new, t_out_new, gamma_new, ana_report);
    };
  };
  app_loop(Hole, t, gamma, ana_report);
}
and process_asc = (e, t2, t, gamma, ana_report, return) => {
  switch (merge(t, t2)) {
  | Success(t3) =>
    let ana_report_new =
      AnaAsc({
        location: (),
        exp: e,
        typ: t3,
        t_annotated: t2,
        t_expected: t,
        ana_report,
      });
    let (return_t, return_gamma, syn_report) =
      process(e, t3, gamma, ana_report_new);
    let syn_report = SynAsc({location: (), exp: e, typ: t, syn_report});
    return(return_t, return_gamma, syn_report);
  | Fail(report) =>
    print_endline(string_of_merge_report(report));
    failwith("error");
  };
};

// Testing

let test = (e: exp) => {
  print_endline(string_of_exp(e));
  let (t, gamma, syn_report) = process(e, Hole, Nil, AnaHole);
  print_endline(string_of_typ(t));
  print_endline(string_of_context(gamma));
  switch (gamma) {
  | Nil => ()
  | Cons((_, _, report), _) =>
    print_endline(string_of_context_report(report))
  };
  let _ = syn_report;
  ();
  // print_endline(string_of_syn_report(syn_report));
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

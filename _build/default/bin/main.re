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
let match_arrow = (t: typ): (typ, typ) => {
  switch (t) {
  | Fun(t1, t2) => (t1, t2)
  | Hole => (Hole, Hole)
  | Base => failwith("no")
  };
};

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
let rec merge = (t1: typ, t2: typ): typ => {
  switch (t1, t2) {
  | (Base, Base) => Base
  | (Hole, t2) => t2
  | (t1, Hole) => t1
  | (Fun(t1, t2), Fun(t3, t4)) => Fun(merge(t1, t3), merge(t2, t4))
  | (Base, Fun(_, _)) => failwith("no")
  | (Fun(_, _), Base) => failwith("no")
  };
};

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
let rec context_add = (gamma: context, x: var, t: typ): context => {
  switch (gamma) {
  | Nil => Cons((x, t), Nil)
  | Cons((y, _), gamma2) when x == y => Cons((x, t), gamma2)
  | Cons(pair, gamma2) => Cons(pair, context_add(gamma2, x, t))
  };
};
let rec context_search = (gamma: context, x: var): typ => {
  switch (gamma) {
  | Nil => failwith("no")
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
  | Cons((y, t2), gamma2) when x == y => Cons((x, merge(t, t2)), gamma2)
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

let rec process = (e: exp, t: typ, gamma: context): (typ, context) => {
  print_endline(
    string_of_context(gamma)
    ++ " |- "
    ++ string_of_typ(t)
    ++ " => "
    ++ string_of_exp(e),
  );
  let return = (return_t: typ, return_gamma: context): (typ, context) => {
    print_endline(
      string_of_context(gamma)
      ++ " |- "
      ++ string_of_typ(t)
      ++ " => "
      ++ string_of_exp(e)
      ++ " => "
      ++ string_of_typ(return_t)
      ++ " -| "
      ++ string_of_context(return_gamma),
    );
    (return_t, return_gamma);
  };
  switch (e) {
  | Var(x) =>
    let t2 = merge(context_search(gamma, x), t);
    return(t2, context_add(gamma, x, t2));
  | Fun(x, e) =>
    let (t1, t2) = match_arrow(t);
    let (t3, gamma2) = process(e, t2, context_add(gamma, x, t1));
    return(Fun(context_search(gamma2, x), t3), context_remove(gamma2, x));
  | App(e1, e2) =>
    let (t2, gamma2) = process(e1, Fun(Hole, t), gamma);
    let (t3, t4) = match_arrow(t2);

    let (t5, gamma3) = process(e2, t3, gamma2);
    let gamma4 = context_merge(gamma2, gamma3);

    let (t6, gamma5) = process(e1, Fun(t5, t4), gamma4);
    let (_, t8) = match_arrow(t6);

    let final_t: typ = t8;
    let final_gamma = context_merge(gamma4, gamma5);
    if (final_t == t && final_gamma == gamma) {
      return(t, gamma);
    } else {
      let (return_t, return_gamma) = process(e, final_t, final_gamma);
      return(return_t, return_gamma);
    };
  | Asc(e, t2) =>
    let (return_t, return_gamma) = process(e, merge(t, t2), gamma);
    return(return_t, return_gamma);
  };
};

// let let_exp = (x: var, e1: exp, e2: exp): exp => App(Fun(x, e2), e1);
let const = (x: var, t: typ, e: exp): exp => Asc(Fun(x, e), Fun(t, Hole));
let example_term =
  const(
    "+",
    Fun(Base, Fun(Base, Base)),
    const(
      "0",
      Base,
      Fun(
        "a",
        Fun(
          "b",
          Fun(
            "c",
            App(
              App(
                Var("+"),
                App(Var("a"), App(Var("b"), App(Var("c"), Var("0")))),
              ),
              App(Var("c"), App(Var("b"), App(Var("a"), Var("0")))),
            ),
          ),
        ),
      ),
    ),
  );
print_endline(string_of_exp(example_term));

// let example_term2 =
//   const(
//     "+",
//     Fun(Base, Fun(Base, Base)),
//     const("0", Base, App(Var("+"), Var("0"))),
//   );

let (t, gamma) = process(example_term, Hole, Nil);
print_endline(string_of_typ(t));
print_endline(string_of_context(gamma));

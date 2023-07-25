// Datatypes
type var = string;
type history =
  | IDK
  | FreeUse
  | Ascription(exp, outer_typ)
  | Error
  | ArrowHole(history)
  | ArrowIn(history)
  | ArrowOut(history)
  | AppArrow(exp)
  | AppArgOver(history, exp)
  | AppFunOver(history, exp)
and annotation_item = (option(var), history)
and annotated_typ('a) =
  | Hole
  | Base
  | Arrow(annotation('a), annotation('a))
and annotation('a) = (annotated_typ('a), 'a)
and typ = annotation(annotation_item)
and exp =
  | Var(var)
  | Asc(exp, typ)
  | Fun(var, exp)
  | App(exp, exp)
and outer_typ =
  | OutHole
  | OutBase
  | OutArrow(outer_typ, outer_typ);
type outer_exp =
  | Var(var)
  | Asc(outer_exp, outer_typ)
  | Fun(var, outer_exp)
  | App(outer_exp, outer_exp);

type context = list((var, typ));
type merge_result =
  | Success(typ)
  | Fail(typ);
type error = unit;

let rec typ_of_outer =
        (e: exp, t: outer_typ, t_acc: outer_typ => outer_typ): typ => {
  switch (t) {
  | OutHole => (Hole, (None, Ascription(e, t_acc(OutHole))))
  | OutBase => (Base, (None, Ascription(e, t_acc(OutBase))))
  | OutArrow(t1, t2) => (
      Arrow(
        typ_of_outer(e, t1, c => t_acc(OutArrow(c, OutHole))),
        typ_of_outer(e, t2, c => t_acc(OutArrow(OutHole, c))),
      ),
      (None, Ascription(e, t_acc(OutArrow(OutHole, OutHole)))),
    )
  };
};
let rec exp_of_outer = (e: outer_exp): exp => {
  switch (e) {
  | Var(x) => Var(x)
  | Asc(e, t) =>
    let e2 = exp_of_outer(e);
    Asc(e2, typ_of_outer(e2, t, c => c));
  | Fun(x, e) => Fun(x, exp_of_outer(e))
  | App(e1, e2) => App(exp_of_outer(e1), exp_of_outer(e2))
  };
};

// Utility functions
let typ_equal = ((typ1, _): typ, (typ2, _): typ): bool => {
  typ1 == typ2;
};
let rec merge = (typ1: typ, typ2: typ): merge_result => {
  let (t1, a1) = typ1;
  let (t2, a2) = typ2;
  switch (t1, t2) {
  | (Base, Base) => Success((Base, a1))
  | (Hole, t2) => Success((t2, a2))
  | (t1, Hole) => Success((t1, a1))
  | (Arrow(t3, t4), Arrow(t5, t6)) =>
    switch (merge(t3, t5), merge(t4, t6)) {
    | (Success(t7), Success(t8)) => Success((Arrow(t7, t8), a1))
    | (Fail(t7), Success(t8))
    | (Success(t7), Fail(t8))
    | (Fail(t7), Fail(t8)) => Fail((Arrow(t7, t8), a1))
    }
  | (Base, Arrow(_, _))
  | (Arrow(_, _), Base) => Fail((Hole, (None, Error)))
  };
};
let match_arrow = ((t, (v, h)): typ): option((typ, typ)) => {
  switch (t) {
  | Arrow(t1, t2) => Some((t1, t2))
  | Hole => Some(((Hole, (v, ArrowHole(h))), (Hole, (v, ArrowHole(h)))))
  | Base => None
  };
};
let context_get = (gamma: context, x: var): typ => {
  switch (List.assoc_opt(x, gamma)) {
  | Some(typ) => typ
  | None => (Hole, (Some(x), FreeUse))
  };
};
let context_add = (gamma: context, x: var, t: typ): context => {
  let gamma' = List.remove_assoc(x, gamma);
  [(x, t), ...gamma'];
};
let rec context_merge_item =
        (gamma: context, x: var, t: typ): (context, list(error)) => {
  switch (gamma) {
  | [] => ([(x, t)], [])
  | [(y, t2), ...gamma2] when x == y =>
    switch (merge(t, t2)) {
    | Success(t3) => ([(x, t3), ...gamma2], [])
    | Fail(t3) => ([(x, t3), ...gamma2], [()])
    }
  | [item, ...gamma2] =>
    let (gamma3, errors) = context_merge_item(gamma2, x, t);
    ([item, ...gamma3], errors);
  };
};
let rec context_merge =
        (gamma1: context, gamma2: context): (context, list(error)) => {
  switch (gamma1) {
  | [] => (gamma2, [])
  | [(x, t), ...gamma3] =>
    let (gamma4, errors1) = context_merge_item(gamma2, x, t);
    let (gamma5, errors2) = context_merge(gamma3, gamma4);
    (gamma5, List.append(errors1, errors2));
  };
};
let item_in_context = ((x, (t, _)), gamma): bool => {
  switch (List.assoc_opt(x, gamma)) {
  | Some((t', _)) => t == t'
  | None => false
  };
};
let rec context_in_context = (gamma1: context, gamma2: context): bool => {
  switch (gamma1, gamma2) {
  | ([], _) => true
  | ([item, ...gamma3], gamma2) =>
    if (item_in_context(item, gamma2)) {
      context_in_context(gamma3, gamma2);
    } else {
      false;
    }
  };
};
let context_equal = (gamma1, gamma2) =>
  context_in_context(gamma1, gamma2) && context_in_context(gamma2, gamma1);

// String functions
let string_of_var = (x: var): string => x;
let rec string_of_history = (h: history): string => {
  switch (h) {
  | IDK => "IDK"
  | FreeUse => "Free Use"
  | Ascription(e, t) =>
    let _ = e;
    Printf.sprintf(
      "Ascription %s : %s",
      //string_of_exp(e),
      "...",
      string_of_outer_typ(t),
    );
  | Error => "Error"
  | ArrowHole(h2) => "Arrow Hole : " ++ string_of_history(h2)
  | ArrowIn(h2) =>
    Printf.sprintf("Bound in X, and %s ", string_of_history(h2))
  | ArrowOut(h2) =>
    Printf.sprintf("Body of X, and %s ", string_of_history(h2))
  | AppArrow(e) => Printf.sprintf(" %s(_) appears", string_of_exp(e))
  | AppArgOver(h2, e) =>
    Printf.sprintf(
      " F(%s) appears, and %s",
      string_of_exp(e),
      string_of_history(h2),
    )
  | AppFunOver(h2, e) =>
    Printf.sprintf(
      " %s(A) appears, and %s",
      string_of_exp(e),
      string_of_history(h2),
    )
  };
}
and string_of_typ = ((t, _): typ): string => {
  switch (t) {
  | Base => "B"
  | Hole => "?"
  | Arrow(t1, t2) =>
    "(" ++ string_of_typ(t1) ++ " -> " ++ string_of_typ(t2) ++ ")"
  };
}
and string_of_outer_typ = (t: outer_typ): string => {
  switch (t) {
  | OutBase => "B"
  | OutHole => "?"
  | OutArrow(t1, t2) =>
    "("
    ++ string_of_outer_typ(t1)
    ++ " -> "
    ++ string_of_outer_typ(t2)
    ++ ")"
  };
}
and string_of_typ_history = ((t, (_, h)): typ): string => {
  (
    switch (t) {
    | Base => "B"
    | Hole => "?"
    | Arrow(t1, t2) =>
      "("
      ++ string_of_typ_history(t1)
      ++ " -> "
      ++ string_of_typ_history(t2)
      ++ ")"
    }
  )
  ++ " [because : "
  ++ string_of_history(h)
  ++ "]";
}
and string_of_exp = (e: exp): string => {
  switch (e) {
  | Var(x) => string_of_var(x)
  | Asc(Fun(x, e), (Arrow(t1, t2), _)) =>
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
  | [] => "."
  | [(x, t)] => string_of_var(x) ++ ": " ++ string_of_typ(t)
  | [(x, t), ...gamma] =>
    string_of_context([(x, t)]) ++ ", " ++ string_of_context(gamma)
  };
};
let rec string_of_context_history = (gamma: context): string => {
  switch (gamma) {
  | [] => "."
  | [(x, t)] => string_of_var(x) ++ ": " ++ string_of_typ_history(t)
  | [(x, t), ...gamma] =>
    string_of_context_history([(x, t)])
    ++ ", "
    ++ string_of_context_history(gamma)
  };
};

// Main function: process
let rec process =
        (e: exp, t: typ, gamma: context): (typ, context, list(error)) => {
  switch (e) {
  | Var(x) => process_var(x, t, gamma)
  | Asc(e, t2) => process_asc(e, t2, t, gamma)
  | Fun(x, e) => process_fun(x, e, t, gamma)
  | App(e1, e2) => process_app(e1, e2, t, gamma)
  };
}
and process_var =
    (x: var, t: typ, gamma: context): (typ, context, list(error)) => {
  let context_t = context_get(gamma, x);
  switch (merge(context_t, t)) {
  | Success(t2) => (t2, context_add(gamma, x, t2), [])
  | Fail(t2) => (t2, gamma, [()])
  };
}
and process_asc =
    (e: exp, t2: typ, t: typ, gamma: context): (typ, context, list(error)) => {
  switch (merge(t, t2)) {
  | Success(t3) =>
    let (return_t, return_gamma, errors) = process(e, t3, gamma);
    (return_t, return_gamma, errors);
  | Fail(t3) => (t3, gamma, [()])
  };
}
and process_fun =
    (x: var, e: exp, t: typ, gamma: context): (typ, context, list(error)) => {
  let (_, a) = t;
  switch (match_arrow(t)) {
  | Some((t1', t2')) =>
    let (t1_in, (v1, h1)) = t1';
    let (t2_in, (v2, h2)) = t2';
    let t1 = (t1_in, (v1, ArrowIn(h1)));
    let t2 = (t2_in, (v2, ArrowOut(h2)));
    let (t3, gamma2, errors) = process(e, t2, context_add(gamma, x, t1));
    let gamma_x = context_get(gamma2, x);
    ((Arrow(gamma_x, t3), a), List.remove_assoc(x, gamma2), errors);
  | None => (t, gamma, [()])
  };
}
and process_app =
    (e1: exp, e2: exp, t: typ, gamma: context): (typ, context, list(error)) => {
  let app_helper =
      (t_in: typ, t_out: typ, gamma: context)
      : (typ, typ, context, list(error)) => {
    let (t2, gamma2, errors1) =
      process(e1, (Arrow(t_in, t_out), (None, AppArrow(e1))), gamma);
    switch (match_arrow(t2)) {
    | Some((t_in_intermediate, t_out_new)) =>
      let t_in_intermediate =
        if (t_in_intermediate == t_in) {
          t_in_intermediate;
        } else {
          let (t_in_intermediate, (opt, h)) = t_in_intermediate;
          (t_in_intermediate, (opt, AppFunOver(h, e1)));
        };
      let (t_in_new, gamma3, errors2) =
        process(e2, t_in_intermediate, gamma2);
      let t_in_new =
        if (t_in_new == t_in_intermediate) {
          t_in_new;
        } else {
          let (t_in_new, (opt, h)) = t_in_new;
          (t_in_new, (opt, AppArgOver(h, e2)));
        };
      let (gamma4, errors3) = context_merge(gamma2, gamma3);
      (
        t_in_new,
        t_out_new,
        gamma4,
        List.concat([errors1, errors2, errors3]),
      );
    | None => (t_in, t_out, gamma2, List.append(errors1, [()]))
    };
  };
  let rec app_loop = (t_in: typ, t_out: typ, gamma: context) => {
    let (t_in_new, t_out_new, gamma_new, errors_new) =
      app_helper(t_in, t_out, gamma);
    if (typ_equal(t_in_new, t_in)
        && typ_equal(t_out_new, t_out)
        && context_equal(gamma_new, gamma)) {
      (t_out_new, gamma_new, errors_new);
    } else {
      app_loop(t_in_new, t_out_new, gamma_new);
    };
  };
  app_loop((Hole, (None, IDK)), t, gamma);
};

// Examples and testing
let test = (e: outer_exp) => {
  let e = exp_of_outer(e);
  let (t, gamma, errors) = process(e, (Hole, (None, IDK)), []);
  let _ = t;
  let _ = errors;
  Printf.printf(
    "Input term: %s\nOutput context: %s\nContext with history: %s\n",
    string_of_exp(e),
    string_of_context(gamma),
    string_of_context_history(gamma),
  );
};
let let_exp = (x: var, e1: outer_exp, e2: outer_exp): outer_exp =>
  App(Fun(x, e2), e1);
let const = (x: var, t: outer_typ, e: outer_exp): outer_exp =>
  Asc(Fun(x, e), OutArrow(t, OutHole));
let example_term_long: outer_exp =
  const(
    "+",
    OutArrow(OutBase, OutArrow(OutBase, OutBase)),
    const(
      "0",
      OutBase,
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
let failure_example_term =
  const(
    "+",
    OutArrow(OutBase, OutArrow(OutBase, OutBase)),
    const("0", OutBase, let_exp("a", Var("0"), App(Var("a"), Var("0")))),
  );

let example_id: outer_exp =
  Asc(Fun("x", Var("x")), OutArrow(OutHole, OutBase));

test(example_term_long);
test(failure_example_term);
test(example_id);

let _ = ArrowOut(IDK);
let _ = ArrowIn(IDK);

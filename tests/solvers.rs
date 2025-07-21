use easy_smt::{Context, Response};

fn test_solver_interaction(solver: &mut Context) {
    let int_sort = solver.int_sort();
    let x = solver.declare_const("x", int_sort).unwrap();

    // x <= 2 && x > 1
    let constr = solver.and(
        solver.lte(x, solver.numeral(2)),
        solver.gt(x, solver.numeral(1)),
    );
    solver.assert(constr).unwrap();

    assert_eq!(solver.check().unwrap(), Response::Sat);

    let solution = solver.get_value(vec![x]).unwrap();
    assert_eq!(solution.len(), 1);
    assert_eq!(solution[0].0, x);
    assert_eq!(solver.get_u64(solution[0].1).unwrap(), 2);
}

#[test]
fn test_z3_solver() {
    let mut context = easy_smt::ContextBuilder::new()
        .with_z3_defaults()
        .build()
        .unwrap();
    test_solver_interaction(&mut context);
}

#[test]
fn test_cvc5_solver() {
    let mut context = easy_smt::ContextBuilder::new()
        .with_cvc5_defaults()
        .build()
        .unwrap();
    test_solver_interaction(&mut context);
}

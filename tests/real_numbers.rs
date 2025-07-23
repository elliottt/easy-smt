use easy_smt::{ContextBuilder, Response};

#[test]
fn test_real_numbers() {
    let mut ctx = ContextBuilder::new()
        .solver("z3")
        .solver_args(["-smt2", "-in"])
        .build()
        .unwrap();

    let x = ctx.declare_const("x", ctx.real_sort()).unwrap();
    // x == 2.0
    ctx.assert(ctx.eq(x, ctx.decimal(2.0))).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
    let solution = ctx.get_value(vec![x]).unwrap();
    let sol = ctx.get_f64(solution[0].1).unwrap();
    // Z3 returns `2.0`
    assert_eq!(sol, 2.0);

    let y = ctx.declare_const("y", ctx.real_sort()).unwrap();
    // y == -2.0
    ctx.assert(ctx.eq(y, ctx.decimal(-2.0))).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
    let solution = ctx.get_value(vec![y]).unwrap();
    let sol = ctx.get_f64(solution[0].1).unwrap();
    // Z3 returns `- 2.0`
    assert_eq!(sol, -2.0);

    let z = ctx.declare_const("z", ctx.real_sort()).unwrap();
    // z == 2.5 / 1.0
    ctx.assert(ctx.eq(z, ctx.rdiv(ctx.decimal(2.5), ctx.decimal(1.0))))
        .unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
    let solution = ctx.get_value(vec![z]).unwrap();
    let sol = ctx.get_f64(solution[0].1).unwrap();
    // Z3 returns `(/ 5.0 2.0)`
    assert_eq!(sol, 2.5);

    let a = ctx.declare_const("a", ctx.real_sort()).unwrap();
    // a == 2.5 / -1.0
    ctx.assert(ctx.eq(a, ctx.rdiv(ctx.decimal(2.5), ctx.decimal(-1.0))))
        .unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
    let solution = ctx.get_value(vec![a]).unwrap();
    let sol = ctx.get_f64(solution[0].1).unwrap();
    // Z3 returns `(- (/ 5.0 2.0))`
    assert_eq!(sol, -2.5);
}

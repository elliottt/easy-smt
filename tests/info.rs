use easy_smt::ContextBuilder;

#[test]
fn test_get_info_z3() {
    let mut context = easy_smt::ContextBuilder::new()
        .with_z3_defaults()
        .build()
        .unwrap();

    let solver_name = context
        .get_info(":name")
        .expect("Getting solver name failed");
    assert!(solver_name.is_string());

    let solver_name = context
        .get_str(solver_name)
        .expect("Expected name of the solver");

    assert_eq!(solver_name, "Z3");
}

#[test]
fn test_get_option() {
    let mut ctx = ContextBuilder::new().with_z3_defaults().build().unwrap();

    ctx.set_option(":produce-models", ctx.true_())
        .expect("Failed to set option");

    let opt_val = ctx
        .get_option(":produce-models")
        .expect("Failed to get value of option");
    assert_eq!(ctx.get_bool(opt_val), Some(true));
}

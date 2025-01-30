
// This test ensures that we can handle `(error "...")` responses from z3.
#[test]
fn handles_errors_gracefully() -> std::io::Result<()> {
    let mut context = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()?;

    let width = context.numeral(1);
    let sort = context.bit_vec_sort(width);

    // The name `foo:a` will cause a parse error, as z3 will parse it as the two atoms, `foo`
    // and `:a`, and then reject the invalid declaration.
    context.declare_fun("foo:a", vec![], sort).expect_err("z3 should reject this declaration");

    Ok(())
}


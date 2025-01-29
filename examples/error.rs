fn main() -> std::io::Result<()> {
    let mut context = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()?;

    let width = context.numeral(1);
    let sort = context.bit_vec_sort(width);
    context.declare_fun("foo:a", vec![], sort).expect_err("z3 should reject this declaration");

    Ok(())
}

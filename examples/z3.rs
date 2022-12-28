
use easy_smt::SExpr;

fn main() -> std::io::Result<()> {

    let mut solver = easy_smt::Solver::new("z3", ["-smt2", "-in"])?;
    let x = solver.declare("x", SExpr::atom("Int"))?;
    solver.assert(SExpr::equal(x.clone(), SExpr::atom("10")))?;

    solver.check()?;

    let vals = solver.get_value(vec![x])?;
    println!("model: {:?}", vals);

    Ok(())

}

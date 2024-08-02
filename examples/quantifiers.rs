// In this example, we assert quantified formulas over uninterpreted
// sorts and functions.

fn main() -> std::io::Result<()> {
    env_logger::init();
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()?;

    // Declare an uninterpreted representation for sets.
    ctx.declare_sort("MySet", 0)?;
    // Declare representation for elements of those sets.
    ctx.declare_sort("MyElement", 0)?;

    // Our sets have a simple interface of predicates: empty(s),
    // member(x,s), and subset(s1,s2).
    ctx.declare_fun(
        "empty",
        vec![ctx.atom("MySet")],
        ctx.bool_sort(),
    )?;
    ctx.declare_fun(
        "member",
        vec![ctx.atom("MyElement"), ctx.atom("MySet")],
        ctx.bool_sort(),
    )?;
    ctx.declare_fun(
        "subset",
        vec![ctx.atom("MySet"), ctx.atom("MySet")],
        ctx.bool_sort(),
    )?;

    // We assert some simple axioms on this interface.

    // First, a set s1 is either a subset of s2, or a member of s1
    // exists which is not a member of s2.
    ctx.assert(
        // For any pair of sets,
        ctx.forall(
            [("s1", ctx.atom("MySet")), ("s2", ctx.atom("MySet"))],
            // One of the following is true:
            ctx.or(
                // (1) s1 is a subset of s2, or
                ctx.list(vec![
                    ctx.atom("subset"),
                    ctx.atom("s1"),
                    ctx.atom("s2"),
                ]),
                // (2) an element exists which is a member of s1, and
                // not a member of s2.
                ctx.exists(
                    [("x", ctx.atom("MyElement"))],
                    ctx.and(
                        ctx.list(vec![
                            ctx.atom("member"),
                            ctx.atom("x"),
                            ctx.atom("s1"),
                        ]),
                        ctx.not(ctx.list(vec![
                            ctx.atom("member"),
                            ctx.atom("x"),
                            ctx.atom("s2"),
                        ])),
                    ),
                ),
            ),
        )
    )?;

    // Second, a set is empty iff no member exists.
    ctx.assert(
        // For any set,
        ctx.forall(
            [("s1", ctx.atom("MySet"))],
            // The following formulas are equivalent:
            ctx.eq(
                // (1) the set is not empty, and
                ctx.not(ctx.list(vec![ctx.atom("empty"), ctx.atom("s1")])),
                // (2) an element exists that is a member of the set.
                ctx.exists(
                    [("x", ctx.atom("MyElement"))],
                    ctx.list(vec![
                        ctx.atom("member"),
                        ctx.atom("x"),
                        ctx.atom("s1"),
                    ]),
                ),
            ),
        ),
    )?;

    // Now, let's check whether a relationship between two sets is
    // possible.
    ctx.declare_const("s1", ctx.atom("MySet"))?;
    ctx.declare_const("s2", ctx.atom("MySet"))?;

    // Is it possible for s1 to be empty,
    ctx.assert(
        ctx.list(vec![ctx.atom("empty"), ctx.atom("s1")])
    )?;
    // while also s1 is not a subset of s2?
    ctx.assert(
        ctx.not(
            ctx.list(vec![
                ctx.atom("subset"),
                ctx.atom("s1"),
                ctx.atom("s2"),
            ])
        )
    )?;

    // We expect the answer to be no (UNSAT).
    match ctx.check()? {
        easy_smt::Response::Sat => {
            println!("Solver returned SAT. This is unexpected!");
        },
        easy_smt::Response::Unsat => {
            println!("Solver returned UNSAT. This is expected.");
        },
        easy_smt::Response::Unknown => {
            println!("Solver returned UNKNOWN. This is unexpected!");
        },
    }
    Ok(())
}

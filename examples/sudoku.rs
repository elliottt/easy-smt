use std::collections::HashMap;

use easy_smt::SExpr;

fn main() -> std::io::Result<()> {
    let mut ctx = easy_smt::Context::new("z3", ["-smt2", "-in"])?;

    // for helping diagnose unsolvable problems
    ctx.set_option(":produce-unsat-cores", ctx.true_())?;

    let mut cols = Vec::with_capacity(9);

    // introduce variables for each cell of the game board.
    for x in 0..9 {
        let mut col = Vec::with_capacity(9);
        for y in 0..9 {
            let cell = ctx.declare(&format!("cell_{}_{}", x, y), ctx.int_sort())?;
            ctx.assert(ctx.and(ctx.gt(cell, ctx.i32(0)), ctx.lte(cell, ctx.i32(9))))?;
            col.push(cell);
        }
        cols.push(col);
    }

    // assert row and column constraints
    for (x, col) in cols.iter().enumerate() {
        for y in 0..9 {
            let cell = col[y].clone();
            for i in y + 1..9 {
                ctx.assert(ctx.named(
                    format!("col_{}_{}_{}", x, y, i),
                    ctx.not(ctx.eq(cell, col[i])),
                ))?;
            }
        }
    }

    for y in 0..9 {
        for x in 0..9 {
            let cell = cols[x][y].clone();
            for i in x + 1..9 {
                ctx.assert(ctx.named(
                    format!("row_{}_{}_{}", y, x, i),
                    ctx.not(ctx.eq(cell, cols[i][y])),
                ))?;
            }
        }
    }

    // assert the sub-grid constraints
    let mut cells: Vec<(usize, usize)> = Vec::with_capacity(9);
    for sx in 0..3 {
        let ox = sx * 3;
        for sy in 0..3 {
            cells.clear();
            let oy = sy * 3;
            for x in ox..ox + 3 {
                for y in oy..oy + 3 {
                    cells.push((x, y));
                }
            }

            for (i, (x1, y1)) in cells.iter().enumerate() {
                let cell = cols[*x1][*y1];
                for (x2, y2) in cells.iter().skip(i + 1) {
                    let other = cols[*x2][*y2];
                    ctx.assert(ctx.named(
                        format!("subgrid_{}_{}_{}_{}", x1, y1, x2, y2),
                        ctx.not(ctx.eq(cell, other)),
                    ))?
                }
            }
        }
    }

    // push a context, as we've now asserted the basic rules of the game
    ctx.push()?;

    // assert the board state from the wikipedia page on sudoku
    let mut set = |x: usize, y: usize, val: i32| {
        ctx.assert(ctx.named(
            format!("input_{}_{}", x, y),
            ctx.eq(cols[x][y], ctx.i32(val)),
        ))
    };
    set(0, 0, 5)?;
    set(0, 1, 3)?;
    set(0, 4, 7)?;

    set(1, 0, 6)?;
    set(1, 3, 1)?;
    set(1, 4, 9)?;
    set(1, 5, 5)?;

    set(2, 1, 9)?;
    set(2, 2, 8)?;
    set(2, 7, 6)?;

    set(3, 0, 8)?;
    set(3, 4, 6)?;
    set(3, 8, 3)?;

    set(4, 0, 4)?;
    set(4, 3, 8)?;
    set(4, 5, 3)?;
    set(4, 8, 1)?;

    set(5, 0, 7)?;
    set(5, 4, 2)?;
    set(5, 8, 6)?;

    set(6, 1, 6)?;
    set(6, 6, 2)?;
    set(6, 7, 8)?;

    set(7, 3, 4)?;
    set(7, 4, 1)?;
    set(7, 5, 9)?;
    set(7, 8, 5)?;

    set(8, 4, 8)?;
    set(8, 7, 7)?;
    set(8, 8, 9)?;

    match ctx.check()? {
        easy_smt::Response::Sat => {
            println!("solved!");
            let board: Vec<_> = cols.iter().flatten().cloned().collect();
            let solution: HashMap<SExpr, SExpr> = HashMap::from_iter(ctx.get_value(board)?);
            for x in 0..9 {
                if x % 3 == 0 {
                    println!("+-------+-------+-------+");
                }
                for y in 0..9 {
                    if y % 3 == 0 {
                        print!("| ");
                    }
                    print!("{} ", ctx.display(*solution.get(&cols[x][y]).unwrap()));
                }
                println!("|");
            }
            println!("+-------+-------+-------+");
        }
        easy_smt::Response::Unsat => {
            println!("unsolvable!");
            let unsat_core = ctx.get_unsat_core()?;
            println!("{}", ctx.display(unsat_core));
        }
        easy_smt::Response::Unknown => {
            println!("Unknown?");
        }
    }

    Ok(())
}

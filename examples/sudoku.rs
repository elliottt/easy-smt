use std::collections::HashMap;

use easy_smt::SExpr;

fn main() -> std::io::Result<()> {
    let mut solver = easy_smt::Solver::new("z3", ["-smt2", "-in"])?;

    // for helping diagnose unsolvable problems
    solver.set_option(":produce-unsat-cores", "true")?;

    let mut cols = Vec::with_capacity(9);

    // introduce variables for each cell of the game board.
    for x in 0..9 {
        let mut col = Vec::with_capacity(9);
        for y in 0..9 {
            let cell = solver.declare(&format!("cell_{}_{}", x, y), SExpr::atom("Int"))?;
            solver.assert(SExpr::and([
                cell.clone().gt(SExpr::from(0)),
                cell.clone().lte(SExpr::from(9)),
            ]))?;
            col.push(cell);
        }
        cols.push(col);
    }

    // assert row and column constraints
    for (x, col) in cols.iter().enumerate() {
        for y in 0..9 {
            let cell = col[y].clone();
            for i in y + 1..9 {
                solver.assert(
                    cell.clone()
                        .equal(col[i].clone())
                        .not()
                        .named(format!("col_{}_{}_{}", x, y, i)),
                )?;
            }
        }
    }

    for y in 0..9 {
        for x in 0..9 {
            let cell = cols[x][y].clone();
            for i in x + 1..9 {
                solver.assert(
                    cell.clone()
                        .equal(cols[i][y].clone())
                        .not()
                        .named(format!("row_{}_{}_{}", y, x, i)),
                )?;
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
                let cell = &cols[*x1][*y1];
                for (x2, y2) in cells.iter().skip(i + 1) {
                    let other = &cols[*x2][*y2];
                    solver.assert(
                        cell.clone()
                            .equal(other.clone())
                            .not()
                            .named(format!("subgrid_{}_{}_{}_{}", x1, y1, x2, y2)),
                    )?
                }
            }
        }
    }

    // push a context, as we've now asserted the basic rules of the game
    solver.push()?;

    // assert the board state from the wikipedia page on sudoku
    let mut set = |x: usize, y: usize, val: usize| {
        solver.assert(
            cols[x][y]
                .clone()
                .equal(SExpr::from(val))
                .named(format!("input_{}_{}", x, y)),
        )
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

    match solver.check()? {
        easy_smt::Response::Sat => {
            println!("solved!");
            let board: Vec<_> = cols.iter().flatten().cloned().collect();
            let solution: HashMap<SExpr, SExpr> = HashMap::from_iter(solver.get_value(board)?);
            for x in 0..9 {
                if x % 3 == 0 {
                    println!("+-------+-------+-------+");
                }
                for y in 0..9 {
                    if y % 3 == 0 {
                        print!("| ");
                    }
                    print!("{} ", solution.get(&cols[x][y]).unwrap());
                }
                println!("|");
            }
            println!("+-------+-------+-------+");
        }
        easy_smt::Response::Unsat => {
            println!("unsolvable!");
            println!("{}", solver.get_unsat_core()?);
        }
        easy_smt::Response::Unknown => {
            println!("Unknown?");
        }
    }

    Ok(())
}

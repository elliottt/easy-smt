use easy_smt::{ContextBuilder, Response};

#[test]
fn test_bv_rotate_identity_z3() {
    let mut ctx = ContextBuilder::new()
        .with_z3_defaults()
        .build()
        .unwrap();

    let bv = ctx.declare_const("x", ctx.bit_vec_sort(ctx.numeral(32))).unwrap();
    let rot_left = ctx.rotate_left(4, bv);
    let rot_right = ctx.rotate_right(4, rot_left);
    ctx.assert(ctx.eq(bv, rot_right)).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
}

#[test]
fn test_bv_rotate_identity_cvc5() {
    let mut ctx = ContextBuilder::new()
        .with_cvc5_defaults()
        .build()
        .unwrap();

    let bv = ctx.declare_const("x", ctx.bit_vec_sort(ctx.numeral(32))).unwrap();
    let rot_left = ctx.rotate_left(4, bv);
    let rot_right = ctx.rotate_right(4, rot_left);
    ctx.assert(ctx.eq(bv, rot_right)).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
}

#[test]
fn test_bv_zero_extend_z3() {
    let mut ctx = ContextBuilder::new()
        .with_z3_defaults()
        .build()
        .unwrap();

    let bv = ctx.declare_const("x", ctx.bit_vec_sort(ctx.numeral(8))).unwrap();
    ctx.assert(ctx.eq(bv, ctx.binary(8, 0xFF))).unwrap();
    // Extend *by* 8 bits, making the input 16 bits total
    let ext = ctx.zero_extend(8, bv);
    let expected = ctx.binary(16, 0x00FF);
    ctx.assert(ctx.eq(ext, expected)).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
}

#[test]
fn test_bv_zero_extend_cvc5() {
    let mut ctx = ContextBuilder::new()
        .with_cvc5_defaults()
        .build()
        .unwrap();

    let bv = ctx.declare_const("x", ctx.bit_vec_sort(ctx.numeral(8))).unwrap();
    ctx.assert(ctx.eq(bv, ctx.binary(8, 0xFF))).unwrap();
    // Extend *by* 8 bits, making the input 16 bits total
    let ext = ctx.zero_extend(8, bv);
    let expected = ctx.binary(16, 0x00FF);
    ctx.assert(ctx.eq(ext, expected)).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Sat);
}

#[test]
fn test_bv_nor_z3() {
    let mut ctx = ContextBuilder::new()
        .with_z3_defaults()
        .build()
        .unwrap();

    let bv = ctx.declare_const("x", ctx.bit_vec_sort(ctx.numeral(8))).unwrap();
    let nor_bv = ctx.bvnor(bv, bv);
    ctx.assert(ctx.eq(bv, nor_bv)).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Unsat);
}

#[test]
fn test_bv_nor_cvc5() {
    let mut ctx = ContextBuilder::new()
        .with_cvc5_defaults()
        .build()
        .unwrap();

    let bv = ctx.declare_const("x", ctx.bit_vec_sort(ctx.numeral(8))).unwrap();
    let nor_bv = ctx.bvnor(bv, bv);
    ctx.assert(ctx.eq(bv, nor_bv)).unwrap();
    assert_eq!(ctx.check().unwrap(), Response::Unsat);
}

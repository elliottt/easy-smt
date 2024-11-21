use crate::{sexpr::Arena, SExpr};

macro_rules! for_each_known_atom {
    ( $mac:ident ) => {
        $mac! {
            check_sat: "check-sat";
            check_sat_assuming: "check-sat-assuming";
            unsat: "unsat";
            sat: "sat";
            unknown: "unknown";
            declare_const: "declare-const";
            declare_datatype: "declare-datatype";
            declare_datatypes: "declare-datatypes";
            par: "par";
            declare_sort: "declare-sort";
            declare_fun: "declare-fun";
            define_fun: "define-fun";
            assert: "assert";
            get_model: "get-model";
            get_value: "get-value";
            get_unsat_core: "get-unsat-core";
            set_logic: "set-logic";
            set_option: "set-option";
            exit: "exit";
            push: "push";
            pop: "pop";
            bool: "Bool";
            bang: "!";
            success: "success";
            t: "true";
            f: "false";
            not: "not";
            imp: "=>";
            and: "and";
            or: "or";
            xor: "xor";
            eq: "=";
            distinct: "distinct";
            ite: "ite";
            int: "Int";
            minus: "-";
            plus: "+";
            times: "*";
            div: "div";
            modulo: "mod";
            rem: "rem";
            lte: "<=";
            lt: "<";
            gte: ">=";
            gt: ">";
            array: "Array";
            select: "select";
            store: "store";
            let_: "let";
            forall: "forall";
            exists: "exists";
            match_: "match";
            und: "_";
            bit_vec: "BitVec";
            concat: "concat";
            extract: "extract";
            bvnot: "bvnot";
            bvor: "bvor";
            bvand: "bvand";
            bvnand: "bvnand";
            bvxor: "bvxor";
            bvxnor: "bvxnor";
            bvneg: "bvneg";
            bvadd: "bvadd";
            bvsub: "bvsub";
            bvmul: "bvmul";
            bvudiv: "bvudiv";
            bvurem: "bvurem";
            bvsrem: "bvsrem";
            bvshl: "bvshl";
            bvlshr: "bvlshr";
            bvashr: "bvashr";
            bvule: "bvule";
            bvult: "bvult";
            bvuge: "bvuge";
            bvugt: "bvugt";
            bvsle: "bvsle";
            bvslt: "bvslt";
            bvsge: "bvsge";
            bvsgt: "bvsgt";
        }
    };
}

macro_rules! define_known_atoms {
    ( $( $id:ident : $atom:expr ; )* ) => {
        #[non_exhaustive]
        pub struct KnownAtoms {
            $(
                #[doc = "The atom: `"]
                #[doc = $atom]
                #[doc = "`"]
                pub $id: SExpr,
            )*
        }

        impl KnownAtoms {
            pub(crate) fn new(arena: &Arena) -> Self {
                KnownAtoms {
                    $( $id: arena.atom($atom), )*
                }
            }
        }
    };
}

for_each_known_atom!(define_known_atoms);

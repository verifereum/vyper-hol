(*
 * Type builtins but abi_encode and abi_decode: empty, bounds, convert, extract32.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   type_builtin_expr_ptr_ok
 *)
Theory bodyPtrTypeBuiltins
Ancestors
  bodyPtrTypeBuiltinsResidual exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem type_builtin_expr_ptr_ok:
  !cx v11 tb typ es.
    (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon \/
     tb = Convert \/ tb = Extract32) /\
    (type_builtin_args_length_ok tb (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  cheat
QED

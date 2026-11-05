(*
 * abi_decode.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   abi_decode_expr_ptr_ok
 *)
Theory bodyPtrAbiDecode
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem abi_decode_expr_ptr_ok:
  !cx v11 b typ es.
    (type_builtin_args_length_ok (AbiDecode b) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  cheat
QED

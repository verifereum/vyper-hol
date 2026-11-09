(*
 * abi_encode.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   abi_encode_expr_ptr_ok
 *)
Theory bodyPtrAbiEncode
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem abi_encode_expr_ptr_ok:
  !cx v11 b m typ es.
    (type_builtin_args_length_ok (AbiEncode b m) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 (AbiEncode b m) typ es)
Proof
  cheat
QED

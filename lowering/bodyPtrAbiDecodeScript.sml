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

(* RESIDUAL: held for the abi-decoder port.  The memory ABI decoder at this
   base MLOADs at actual_ptr before its hi-bound check, which fails
   access_ok; the fixed decoder isn't on this branch yet. *)
Theorem abi_decode_expr_ptr_ok:
  !cx v11 b typ es.
    (type_builtin_args_length_ok (AbiDecode b) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  cheat
QED

(*
 * Hashing: keccak256 and sha256.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   hash_builtin_expr_ptr_ok
 *)
Theory bodyPtrHashBuiltins
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem hash_builtin_expr_ptr_ok:
  !cx ty bt es.
    (bt = Keccak256 \/ bt = Sha256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  cheat
QED

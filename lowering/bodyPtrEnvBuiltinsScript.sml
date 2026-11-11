(*
 * Builtins reading the environment, lengths and method ids.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   env_builtin_expr_ptr_ok
 *)
Theory bodyPtrEnvBuiltins
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem env_builtin_expr_ptr_ok:
  !cx ty bt es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/ (?i. bt = Acc i) \/
     bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_ptr_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ptr_ok cx (HD es)) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  cheat
QED

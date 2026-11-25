(* Constructor argument preparation, with the continuation starting at the
   actual prepared compiler cursor. *)
Theory entryCreateCtorStageScope
Ancestors
  entryCreateCompletedCut exprLowering compileEnv vyperInterpreter vyperState

(* The empty ABI list emits neither a row nor an encoder. The continuation
   therefore starts at the original ordinary and shadow cursors. *)
Theorem create_empty_abi_args_scoped_stage:
  scoped_operand_outcome config tops cx st0 a b (next []) (es,s,G,tn) Q R ==>
  compile_create_ctor_args compile_expr ce [] a = ([],a) /\
  compile_create_blueprint_args compile_expr ce F later [] a = ((Lit 0w,Lit 0w),a) /\
  scoped_operand_outcome config tops cx st0 a b (bind (eval_exprs cx []) next)
    (es,s,G,tn) Q R
Proof
  `bind (eval_exprs cx []) next = next []` by
    simp[FUN_EQ_THM, evaluate_def, bind_def, return_def] >>
  simp[compile_create_ctor_args_def, compile_create_blueprint_args_def,
       comp_return_def]
QED

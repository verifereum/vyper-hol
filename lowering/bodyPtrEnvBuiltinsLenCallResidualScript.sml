(* Residual leaf for Len over an internal call whose lowered return type
   differs from the call site's annotation. *)
Theory bodyPtrEnvBuiltinsLenCallResidual
Ancestors
  bodyPtrDefs exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  compileEnv context vyperAST

(* RESIDUAL: Len of an internal-call source under Decision 18; held for the post_value_type_widens port, cf. exprSimLen's len_vv_path *)
Theorem compile_len_singleton_call_sim_ptr:
  !d ctx PG func cenv cx env ty e es.
    post_value_type cenv e <> expr_type e /\
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  cheat
QED

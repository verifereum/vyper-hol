(* Instantiate the body prefix simulation at the selected runtime body. *)
Theory s1PrefixSelectedFrag
Ancestors
  bodyCallLiveness s1PrefixBodySimFullMain loweringRuntimeCorrect

Theorem runtime_selected_body_frag_prefix:
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret_ty,fbody) /\
  ss = subst_consts_stmts (module_consts_env tops []) fbody /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
  supported_stmts tops bindings ss /\
  (!target. supported_stmts_expr_exists
     (expr_abi_decode_target_root target) ss ==>
     occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmts env ret_ty ss = SOME env' /\
  stmts_exprs_ok cenv ss /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmts_env cenv lctx ret_ty ss)
    (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
    (eval_stmts cx ss) es
Proof
  strip_tac >>
  drule_all runtime_selected_body_loop_calls_ok >> strip_tac >>
  `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_stmts ss)` by
    (qpat_assum `ss = subst_consts_stmts _ _` SUBST1_TAC >>
     qpat_assum `source_typing_ok tops am tx`
       (strip_assume_tac o REWRITE_RULE [e2eDefsTheory.source_typing_ok_def]) >>
     drule_then (rewrite_tac o single o CONJUNCT2)
       checked_singleton_subst_int_calls >>
     drule_then ACCEPT_TAC singleton_external_body_calls_live) >>
  qpat_x_assum `ss = subst_consts_stmts _ _` kall_tac >>
  irule body_stmts_sim_prefix >> simp[] >>
  map_every qexists_tac [`bindings`,`env`,`env'`,`tops`] >> asm_rewrite_tac[]
QED

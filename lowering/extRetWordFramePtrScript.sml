Theory extRetWordFramePtr
Ancestors
  extRetWordExactStmtPtr typedCopyPtr compileEnv exprSimHypsDefs
  vyperTypeInvariants vyperTypeSystem finite_map

Theorem external_return_word_frame_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ is_word_type ty /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  expr_sim_ptr d ctx PG func cenv cx ty e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  `well_typed_expr env e /\ expr_type e = ty` by
    (fs[type_stmt_return_some_iff] >> metis_tac[type_widens_to_word]) >>
  irule external_return_word_exact_stmt_frag_ptr >>
  simp[] >> qexists_tac `env` >> simp[] >>
  fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
     env_scopes_consistent_def, well_formed_type_def] >>
  rpt strip_tac >>
  qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> IS_SOME _`
    drule >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ _ ==> evaluate_type _ _ = _` drule_all >>
  simp[]
QED

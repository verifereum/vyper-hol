Theory extRetRawFramePtr
Ancestors
  extRetRawStmtPtr typedCopyPtr compileEnv vyperTypeSystem vyperInterpreter
  vyperTyping exprSimHypsDefs vyperValue vyperTypeCallGraph exprSafeOperand
  vyperTypeInvariants

Theorem arg_type_fits_dynamic_bytes_source[local]:
  !t n. arg_type_fits t (BaseT (BytesT (Dynamic n))) ==>
    ?k. t = BaseT (BytesT (Dynamic k)) /\ k <= n
Proof
  Cases >> simp[arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT b) _` >> Cases_on `b` >>
  simp[arg_type_fits_def] >> rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[arg_type_fits_def]
QED

Theorem external_return_raw_frame_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env (BaseT (BytesT (Dynamic n))) (Return (SOME e))) /\
  is_bytestring_type (lowered_value_type cenv e) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_ptr d ctx PG func cenv cx (BaseT (BytesT (Dynamic n))) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx (BaseT (BytesT (Dynamic n))) (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  `well_typed_expr env e /\ arg_type_fits (expr_type e) (BaseT (BytesT (Dynamic n)))` by
    fs[type_stmt_return_some_iff, type_widens_to_def, arg_type_fits_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
        env_scopes_consistent_def, well_formed_type_def] >>
     rpt strip_tac >>
     qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> IS_SOME _` drule >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     qpat_x_assum `!id ty entry. _ /\ _ ==> evaluate_type _ _ = _` drule_all >> simp[]) >>
  drule_all well_typed_expr_type_well_formed >> strip_tac >>
  drule arg_type_fits_dynamic_bytes_source >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic k)))` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
        well_formed_type_def, evaluate_type_def]) >>
  irule external_return_raw_stmt_frag_ptr >>
  simp[is_word_type_def, is_bytestring_type_def] >>
  conj_tac >- fs[int_calls_stmt_def, int_calls_expr_def] >>
  qexists_tac `env` >> simp[]
QED

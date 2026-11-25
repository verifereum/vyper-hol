(* Typing and source replay facts for a linked constructor snapshot. *)
Theory createCtorSnapshotTypingMods
Ancestors
  exprBodyPreProps exprBodyPreTypingProps exprSimIfExpCompat
  exprReasonOperand exprWordOperand bodySimStmtFacts logArgumentTypeEval
  vyperEvalExprPreservesScopesDom exprSimSource vyperState vyperTypeInvariants
  exprSimHypsDefs vyperTypeSystem exprLowering vyperAST compileEnv valueCopyBytes
  finite_map list

Theorem ctor_snapshot_word_types_mods:
  expr_body_pre_mods mods ce cx env e es ==>
  (is_word_type (lowered_value_type ce e) <=> is_word_type (expr_type e)) /\
  (is_word_type (expr_type e) ==> lowered_value_type ce e = expr_type e)
Proof
  strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[consistent_variable_type_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_mods_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
     ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  drule_all ifexp_lowered_type_classify >> strip_tac
  >- simp[]
  >- metis_tac[is_bytestring_word_type] >>
  PairCases_on `fid` >>
  gvs[well_typed_expr_def, lowered_value_type_def, expr_type_def] >>
  qpat_x_assum `!fid sg. _` (drule_then SUBST1_TAC) >>
  gvs[type_widens_to_def] >>
  metis_tac[abiEncodeArgsSimTheory.abi_args_word_fits_eq,
            aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]
QED

Theorem ctor_snapshot_gas_pre_mods[simp]:
  expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods ce cx env e es
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def, env_consistent_def,
       env_context_consistent_def, state_well_typed_def]
QED

Theorem ctor_snapshot_source_frame_mods:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  expr_sim_inv_mods mods ce cx env ee /\ MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  strip_tac >> conj_tac
  >- (drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> simp[]) >>
  fs[bind_def, AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

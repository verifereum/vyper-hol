(* Request-prefix lemmas for local and top-level name lookup in value and VV form. *)
Theory s1PrefixNames
Ancestors
  s1PrefixFrame s1PrefixDefs vyperStorageTrace vyperInterpreter
  vyperEvalMisc vyperStatePreservation vyperState vyperAST list

Theorem name_value_prefix:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Name ann id) es
Proof
  rw[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt gen_tac >>
  namedCases_on `eval_expr cx (Name ann id) (es with gas_obs := gobs)`
    ["name_result eval_state"] >>
  drule_then SUBST_ALL_TAC eval_expr_Name_preserves_state >>
  Cases_on `name_result` >> simp[bind_def]
  >- (strip_tac >> drule_then SUBST_ALL_TAC read_result_state >> simp[]) >>
  rw[] >> simp[]
QED

Triviality lookup_global_no_outcome:
  lookup_global cx src id st = (res, st') ==>
  EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
    (DROP (LENGTH st.storage_trace) st'.storage_trace)
Proof
  Cases_on `get_module_code cx src` >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `get_module_code cx src = SOME code` >>
  Cases_on `find_var_decl_by_name id code`
  >- (namedCases_on `get_immutables cx src st` ["imm_result eval_state"] >>
      drule_then SUBST_ALL_TAC get_immutables_state >>
      Cases_on `imm_result` >>
      simp[bind_def, return_def, raise_def, vyperMiscTheory.option_CASE_rator,
           AllCaseEqs()] >> rw[] >> simp[]) >>
  rename1 `find_var_decl_by_name id code = SOME decl` >>
  namedCases_on `decl` ["decl_kind decl_name"] >> Cases_on `decl_kind` >>
  simp[bind_def, ignore_bind_def, lift_option_type_def, return_def, raise_def,
       record_storage_event_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rw[] >> simp[DROP_APPEND1]
QED

Theorem toplevel_name_value_prefix:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (TopLevelName ann nsid) es
Proof
  namedCases_on `nsid` ["src id"] >>
  rw[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt gen_tac >> simp[Once evaluate_def] >>
  Cases_on `lookup_global cx src id (es with gas_obs := gobs)` >>
  rename1 `lookup_global _ _ _ _ = (result, mid)` >>
  drule lookup_global_no_outcome >>
  Cases_on `result` >> simp[bind_def]
  >- (rpt strip_tac >> drule_then SUBST_ALL_TAC read_result_state >> simp[]) >>
  rw[] >> simp[]
QED

Theorem toplevel_name_vv_prefix:
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (TopLevelName ann nsid) es
Proof
  namedCases_on `nsid` ["src id"] >>
  rw[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame] >>
  rpt gen_tac >> simp[Once evaluate_def] >>
  strip_tac >> drule lookup_global_no_outcome >> simp[]
QED

Theorem name_vv_prefix:
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Name ann id) es
Proof
  rw[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame] >>
  rpt gen_tac >> strip_tac >>
  drule_then SUBST_ALL_TAC eval_expr_Name_preserves_state >> simp[]
QED

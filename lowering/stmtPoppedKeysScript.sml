(*
 * Statement evaluation keeps popped_keys_indexed
 *
 * TOP-LEVEL:
 *   eval_statement_loop_popped_keys_indexed — eval_stmt, eval_stmts and
 *     eval_for keep popped_keys_indexed: the statement counterpart of
 *     exprSimHyps's eval_expr_popped_keys_indexed
 *
 * Helper:
 *   *_popped_keys_indexed — one lemma per scope write (push_scope,
 *     pop_scope, new_variable, write_place, append_place, ...) and per
 *     statement case of evaluate_ind
 *)

Theory stmtPoppedKeys
Ancestors
  list finite_map exprSimHyps vyperInterpreter vyperState
  vyperPlaceResultTyping vyperScopePreservation vyperLookup
  vyperTypeInvariants vyperPlaceInvariants vyperTypeEvalSoundness
  vyperTypeExprSoundness vyperTypeSystem vyperTypeCallGraph vyperTypeValues
  vyperTypeCallStackSoundness vyperTypeEnvPreservation vyperTypeStatePreservation
Libs
  pairLib


Theorem scope_pop_effect_popped_keys_indexed:
  !f st res st'.
    scope_pop_effect f /\ f st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> gvs[scope_pop_effect_def] >>
  first_x_assum drule >> strip_tac >> gvs[state_well_typed_def] >>
  drule_all scope_pop_trace_keys_indexed >> simp[]
QED

Theorem eval_exprs_popped_keys_indexed:
  !cx es st res st'.
    eval_exprs cx es st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed,
            cj 6 eval_mutual_scope_pop_effect]
QED

Theorem eval_target_place_popped_keys_indexed:
  !cx e st res st'.
    eval_target_place cx e st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed,
            cj 8 eval_mutual_scope_pop_effect]
QED

Theorem popped_keys_indexed_update:
  !pre sc rest id entry.
    popped_keys_indexed (pre ++ sc::rest) /\
    popped_history_typed entry.type entry.popped /\
    EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
      subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n)))
      (MAP FST entry.popped) ==>
    popped_keys_indexed (pre ++ (sc |+ (id,entry))::rest)
Proof
  rw[popped_keys_indexed_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[] >> metis_tac[]
QED

Theorem push_scope_popped_keys_indexed:
  !st res st'.
    push_scope st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rw[push_scope_def, return_def] >> gvs[popped_keys_indexed_def]
QED

Theorem push_scope_with_var_popped_keys_indexed:
  !nm tv v st res st'.
    push_scope_with_var nm tv v st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rw[push_scope_with_var_def, return_def, popped_keys_indexed_def,
     FLOOKUP_UPDATE] >> gvs[FLOOKUP_UPDATE, AllCaseEqs(), popped_history_typed_def]
QED

Theorem pop_scope_popped_keys_indexed:
  !st res st'.
    pop_scope st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `st.scopes` >>
  rw[pop_scope_def, return_def, raise_def, popped_keys_indexed_def] >> gvs[]
QED

Theorem new_variable_popped_keys_indexed:
  !id tv v st res st'.
    new_variable id tv v st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `st.scopes` >>
  simp[new_variable_def, get_scopes_def, set_scopes_def, bind_def,
       ignore_bind_def, return_def, type_check_def, assert_def,
       raise_def, AllCaseEqs()] >>
  rw[] >> gvs[popped_keys_indexed_def, FLOOKUP_UPDATE, AllCaseEqs(),
              popped_history_typed_def] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem eval_iterator_scope_pop_effect[local]:
  !cx it. scope_pop_effect (eval_iterator cx it)
Proof
  `!cx ty tv. scope_pop_effect (array_iterator_results cx ty tv)` by
    (rpt gen_tac >> irule scope_pop_effect_identity >>
     metis_tac[array_iterator_results_state]) >>
  rpt gen_tac >> Cases_on `it` >> simp[Once evaluate_def] >>
  rpt (gen_tac ORELSE
       (irule scope_pop_effect_bind >> conj_tac >>
        simp[cj 5 eval_mutual_scope_pop_effect]))
QED

Theorem eval_iterator_popped_keys_indexed:
  !cx it st res st'.
    eval_iterator cx it st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed, eval_iterator_scope_pop_effect]
QED

Theorem replace_memory_entry_popped:
  !entry path v entry'.
    replace_memory_entry entry path v = INL entry' ==>
    entry' = entry \/ entry'.popped = []
Proof
  rw[replace_memory_entry_def, AllCaseEqs()] >> simp[]
QED

Theorem write_place_popped_keys_indexed:
  !cx p v st res st'.
    write_place cx p v st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `p`
  >- metis_tac[write_storage_place_scopes_immutables]
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
      drule find_containing_scope_structure >> strip_tac >>
      drule replace_memory_entry_popped >> strip_tac >>
      irule popped_keys_indexed_update >>
      gvs[popped_keys_indexed_def, popped_history_typed_def] >> metis_tac[]) >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
           get_immutables_def, get_address_immutables_def, return_def, raise_def]) >>
  metis_tac[set_immutable_scopes]
QED

Theorem append_place_popped_keys_indexed:
  !cx p v st res st'.
    append_place cx p v st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `p`
  >- metis_tac[append_storage_place_scopes_immutables] >>
  simp[append_place_def, bind_def, lift_sum_def, return_def, raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  Cases_on `append_element tv old v` >> gvs[return_def, raise_def] >>
  drule_all write_place_popped_keys_indexed >> simp[]
QED

Theorem assign_tuple_popped_keys_indexed:
  (!cx g v env ty st res st'.
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget g) /\
    assign_tuple_targets cx g v st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!cx gs vs env tys st res st'.
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets gs) /\
    assign_tuple_target_list cx gs vs st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes)
Proof
  `(!(cx:evaluation_context) (s:stmt). T) /\
   (!(cx:evaluation_context) (ss:stmt list). T) /\
   (!(cx:evaluation_context) (it:iterator). T) /\
   (!(cx:evaluation_context) (ty:type_value) (nm:string) (body:stmt list) (vs:eval_result list). T) /\
   (!(cx:evaluation_context) (e:expr). T) /\
   (!(cx:evaluation_context) (es:expr list). T) /\
   (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
   (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
   (!cx g v env ty st res st'.
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget g) /\
    assign_tuple_targets cx g v st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
   (!cx gs vs env tys st res st'.
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets gs) /\
    assign_tuple_target_list cx gs vs st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
   (!(cx:evaluation_context) (es:expr list). T)` suffices_by metis_tac[] >>
  ho_match_mp_tac evaluate_ind >> rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `assign_tuple_targets _ (BaseTarget _) _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      gvs[runtime_consistent_def] >>
      imp_res_tac eval_target_place_popped_keys_indexed >>
      metis_tac[write_place_popped_keys_indexed])
  >- (rpt gen_tac >> strip_tac >> Cases_on `v` >>
      simp[Once evaluate_def, raise_def] >>
      Cases_on `a` >> gvs[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[well_typed_atarget_def, int_calls_atarget_def] >>
      drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def, raise_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  Cases_on `tys` >> gvs[] >>
  gvs[int_calls_atarget_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  qpat_x_assum `assign_tuple_target_list cx _ _ st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `popped_keys_indexed s''.scopes` by (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx s''` by
    (fs[runtime_consistent_def] >>
     drule_all (cj 9 eval_scc_type_sound_mutual) >> simp[]) >>
  qpat_x_assum `!s t. assign_tuple_targets _ _ _ _ = _ ==> _` drule >>
  disch_then drule_all >> simp[]
QED

Theorem stmt_return_popped_keys_indexed:
  !cx e st res st'.
    eval_stmt cx (Return e) st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `e` >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_scopes >> gvs[] >>
  metis_tac[eval_expr_popped_keys_indexed]
QED

Theorem stmt_expr_popped_keys_indexed:
  !cx e st res st'.
    eval_stmt cx (Expr e) st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac type_check_scopes >> gvs[] >>
  metis_tac[eval_expr_popped_keys_indexed]
QED

Theorem stmt_log_popped_keys_indexed:
  !cx id es st res st'.
    eval_stmt cx (Log id es) st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_scopes >> imp_res_tac push_log_scopes >> gvs[] >>
  metis_tac[eval_exprs_popped_keys_indexed]
QED

Theorem stmt_annassign_popped_keys_indexed:
  !cx id typ e st res st'.
    eval_stmt cx (AnnAssign id typ e) st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  gvs[lift_option_type_def, return_def, raise_def] >>
  imp_res_tac read_result_scopes >> gvs[] >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  drule new_variable_popped_keys_indexed >> simp[]
QED

Theorem stmt_raise_scope_pop_effect[local]:
  !cx reason. scope_pop_effect (eval_stmt cx (Raise reason))
Proof
  rpt gen_tac >> Cases_on `reason` >> simp[Once evaluate_def] >>
  rpt (gen_tac ORELSE
       (irule scope_pop_effect_bind >> conj_tac >>
        simp[cj 5 eval_mutual_scope_pop_effect])) >>
  Cases_on `c` >> simp[] >> rename1 `CustomError id positional kwargs` >>
  Cases_on `get_module_code cx (FST id)` >> simp[] >>
  Cases_on `lookup_custom_error_args_in (SND id) x` >> simp[] >>
  Cases_on `order_custom_error_args x' (CustomError id positional kwargs)` >> simp[] >>
  irule scope_pop_effect_bind >> simp[cj 6 eval_mutual_scope_pop_effect] >>
  gen_tac >> irule scope_pop_effect_bind >> simp[]
QED

Theorem stmt_raise_popped_keys_indexed:
  !cx reason st res st'.
    eval_stmt cx (Raise reason) st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed, stmt_raise_scope_pop_effect]
QED

Theorem stmt_assert_scope_pop_effect[local]:
  !cx e reason. scope_pop_effect (eval_stmt cx (Assert e reason))
Proof
  rpt gen_tac >> Cases_on `reason` >> simp[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[cj 5 eval_mutual_scope_pop_effect] >>
  gen_tac >> irule scope_pop_effect_switch >> simp[] >>
  rpt (gen_tac ORELSE
       (irule scope_pop_effect_bind >> conj_tac >>
        simp[cj 5 eval_mutual_scope_pop_effect])) >>
  Cases_on `c` >> simp[] >> rename1 `CustomError id positional kwargs` >>
  Cases_on `get_module_code cx (FST id)` >> simp[] >>
  Cases_on `lookup_custom_error_args_in (SND id) x` >> simp[] >>
  Cases_on `order_custom_error_args x' (CustomError id positional kwargs)` >> simp[] >>
  irule scope_pop_effect_bind >> simp[cj 6 eval_mutual_scope_pop_effect] >>
  gen_tac >> irule scope_pop_effect_bind >> simp[]
QED

Theorem stmt_assert_popped_keys_indexed:
  !cx e reason st res st'.
    eval_stmt cx (Assert e reason) st = (res,st') /\ state_well_typed st /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed, stmt_assert_scope_pop_effect]
QED
Theorem stmt_assign_base_popped_keys_indexed:
  !cx bt e env ret_ty env' st res st'.
    type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
    eval_stmt cx (Assign (BaseTarget bt) e) st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once type_stmt_def, int_calls_stmt_def, int_calls_atarget_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[runtime_consistent_def] >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  drule_all (cj 1 (cj 5 eval_scc_type_sound_mutual)) >>
  strip_tac >> gvs[] >>
  imp_res_tac eval_target_place_popped_keys_indexed >>
  imp_res_tac read_result_scopes >> gvs[] >>
  metis_tac[write_place_popped_keys_indexed]
QED

Theorem stmt_append_popped_keys_indexed:
  !cx bt e env ret_ty env' st res st'.
    type_stmt env ret_ty (Append bt e) = SOME env' /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
    eval_stmt cx (Append bt e) st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once type_stmt_def, AllCaseEqs(), int_calls_stmt_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[runtime_consistent_def] >>
  drule_all eval_target_place_popped_keys_indexed >> strip_tac >>
  drule_all (cj 1 (cj 8 eval_scc_type_sound_mutual)) >> strip_tac >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  imp_res_tac read_result_scopes >> gvs[] >>
  metis_tac[append_place_popped_keys_indexed]
QED

Theorem stmt_augassign_popped_keys_indexed:
  !cx ty bt bop e env ret_ty env' st res st'.
    type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty bt bop e)) /\
    eval_stmt cx (AugAssign ty bt bop e) st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once type_stmt_def, int_calls_stmt_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[runtime_consistent_def] >>
  drule_all eval_target_place_popped_keys_indexed >> strip_tac >>
  drule_all (cj 1 (cj 8 eval_scc_type_sound_mutual)) >> strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >> gvs[] >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  imp_res_tac read_result_scopes >> imp_res_tac lift_sum_scopes >> gvs[] >>
  metis_tac[write_place_popped_keys_indexed]
QED

Theorem stmt_assign_tuple_popped_keys_indexed:
  !cx gs e env ret_ty env' st res st'.
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    eval_stmt cx (Assign (TupleTarget gs) e) st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once type_stmt_def, atarget_accepts_def, int_calls_stmt_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[runtime_consistent_def] >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  rename1 `read_result cx tv middle = (INL v,middle)` >>
  `(do tv <- eval_expr cx e; read_result cx tv od) st = (INL v,middle)` by
    simp[bind_def] >>
  drule_all eval_expr_read_type_sound >> strip_tac >> gvs[] >>
  drule_all (cj 1 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >> gvs[] >>
  irule (cj 1 assign_tuple_popped_keys_indexed) >>
  goal_assum (drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)) >>
  simp[runtime_consistent_def] >> metis_tac[]
QED


Theorem typed_loop_push_runtime[local]:
  evaluate_type env.type_defs ty = SOME tyv /\ value_has_type tyv v /\
  id NOTIN FDOM env.var_types /\ runtime_consistent env cx st /\
  push_scope_with_var id tyv v st = (INL (),stp) ==>
  runtime_consistent (extend_local env id ty F) cx stp
Proof
  strip_tac >> gvs[push_scope_with_var_def, return_def] >>
  fs[runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `well_formed_type_value tyv` by metis_tac[evaluate_type_well_formed_type_value] >>
  conj_tac >- metis_tac[push_scope_with_var_env_consistent] >>
  fs[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem typed_loop_bracket_runtime[local]:
  !env ty tyv v id ret_ty body env_after cx st stp r after.
  evaluate_type env.type_defs ty = SOME tyv /\ value_has_type tyv v /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
  runtime_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  push_scope_with_var id tyv v st = (INL (),stp) /\
  finally (try (do eval_stmts cx body; return F od) handle_loop_exception)
    pop_scope stp = (r,after) ==>
  runtime_consistent env cx after
Proof
  rpt strip_tac >>
  `eval_for cx tyv id body' [Value v] st =
    ((case r of INL b => INL () | INR ex => INR ex),after)` by
    (fs[ignore_bind_def] >>
     simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
     Cases_on `r` >- (rename1 `INL b` >> Cases_on `b` >>
       simp[Once evaluate_def, return_def, bind_def, ignore_bind_def]) >>
     simp[ignore_bind_def, bind_def]) >>
  fs[runtime_consistent_def] >>
  `EVERY (iterator_result_typed tyv) [Value v]` by
    simp[iterator_result_typed_def] >>
  drule_all (cj 4 eval_scc_type_sound_mutual) >> simp[]
QED

Theorem eval_statement_loop_popped_keys_mutual[local]:
  (!cx s env ret_ty env' st res st'.
     type_stmt env ret_ty s = SOME env' /\
     runtime_consistent env cx st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     eval_stmt cx s st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!cx ss env ret_ty env' st res st'.
     type_stmts env ret_ty ss = SOME env' /\
     runtime_consistent env cx st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     eval_stmts cx ss st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!cx tyv id body vs env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (iterator_result_typed tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_for cx tyv id body vs st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!(cx:evaluation_context) (e:expr). T) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- (rpt strip_tac >> gvs[Once evaluate_def, raise_def])
  >- (rpt strip_tac >> gvs[Once evaluate_def, raise_def])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_return_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_return_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_raise_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_raise_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_raise_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_raise_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_assert_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_assert_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_assert_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_assert_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_log_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_annassign_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> drule_all stmt_append_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> drule_all stmt_assign_base_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> drule_all stmt_assign_tuple_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> drule_all stmt_augassign_popped_keys_indexed >> simp[])
  >- suspend "if"
  >- suspend "for"
  >- (rpt strip_tac >> fs[runtime_consistent_def] >>
      drule_all stmt_expr_popped_keys_indexed >> simp[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- suspend "cons"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def]) >>
  suspend "loop"
QED

Resume eval_statement_loop_popped_keys_mutual[cons]:
  rpt strip_tac >>
  gvs[Once type_stmt_def, AllCaseEqs(), int_calls_stmt_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  qpat_x_assum `eval_stmts cx (_::_) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `popped_keys_indexed s''.scopes` by (first_x_assum drule_all >> simp[]) >>
  rename1 `type_stmt env ret_ty s = SOME middle_env` >>
  `runtime_consistent middle_env cx s''` by
    (fs[runtime_consistent_def] >>
     drule_all (cj 1 eval_scc_type_sound_mutual) >> simp[]) >>
  qpat_x_assum `!s t. eval_stmt _ _ _ = _ ==> _` drule >>
  disch_then drule_all >> simp[]
QED

Resume eval_statement_loop_popped_keys_mutual[if]:
  rpt strip_tac >>
  gvs[Once type_stmt_def, int_calls_stmt_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  fs[runtime_consistent_def] >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  drule_all (cj 1 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >> gvs[] >>
  imp_res_tac push_scope_popped_keys_indexed >>
  rename1 `push_scope middle = (INL x,pushed)` >>
  `runtime_consistent env cx pushed` by
    (gvs[push_scope_def, return_def, runtime_consistent_def] >>
     imp_res_tac push_scope_env_consistent >>
     imp_res_tac push_scope_preserves_state_well_typed >>
     metis_tac[push_scope_def, return_def]) >>
  qpat_x_assum `!s tv t s' t'. _`
    (qspecl_then [`st`,`tv`,`middle`,`middle`,`pushed`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!s tv t s' t'. _`
    (qspecl_then [`st`,`tv`,`middle`,`middle`,`pushed`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, switch_BoolV_def, bind_def, COND_RATOR, AllCaseEqs(),
       return_def, raise_def] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `type_stmts env ret_ty ss` >- fs[] >>
  Cases_on `type_stmts env ret_ty ss'` >- fs[] >>
  fs[] >>
  qpat_x_assum `runtime_consistent env cx pushed`
    (strip_assume_tac o REWRITE_RULE [runtime_consistent_def]) >>
  qpat_x_assum `!env1 rt env2 st1 r st2.
    type_stmts env1 rt _ = _ /\ _ ==> _`
    (qspecl_then [`env`,`ret_ty`] mp_tac) >>
  simp[] >> disch_then (qspec_then `pushed` mp_tac) >>
  simp[] >> disch_then assume_tac >>
  qpat_x_assum `!env1 rt env2 st1 r st2.
    type_stmts env1 rt _ = _ /\ _ ==> _`
    (qspecl_then [`env`,`ret_ty`] mp_tac) >>
  simp[] >> disch_then (qspec_then `pushed` mp_tac) >>
  simp[] >> disch_then assume_tac >>
  qpat_x_assum `do pop_scope; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule_all pop_scope_popped_keys_indexed >> simp[]
QED
Resume eval_statement_loop_popped_keys_mutual[for]:
  rpt strip_tac >>
  gvs[Once type_stmt_def, int_calls_stmt_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  fs[runtime_consistent_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, lift_option_type_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  gvs[return_def, raise_def] >>
  imp_res_tac eval_iterator_popped_keys_indexed >>
  gvs[] >>
  drule_all (cj 3 eval_scc_type_sound_mutual) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  gvs[] >>
  Cases_on `type_stmts (extend_local env id typ F) ret_ty body'` >- fs[] >>
  rename1 `eval_iterator cx it start = (INL vs,middle)` >>
  qpat_x_assum `!s vs t s' t'. _`
    (qspecl_then [`start`,`vs`,`middle`,`middle`,`middle`] mp_tac) >>
  simp[check_def, assert_def, return_def] >> strip_tac >>
  metis_tac[]
QED
Resume eval_statement_loop_popped_keys_mutual[loop]:
  rpt strip_tac >> fs[EVERY_DEF] >>
  Cases_on `read_result cx r st` >> rename1 `read_result cx r st = (rd,s_rd)` >>
  drule_all iterator_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `rd`)
  >- (drule eval_for_cons_read_error >> strip_tac >> gvs[]) >>
  gvs[] >> rename1 `read_result cx r st = (INL v,st)` >>
  rpt (first_x_assum (drule_then assume_tac)) >>
  qabbrev_tac `pushed = st with scopes updated_by
    CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))` >>
  `push_scope_with_var id tyv v st = (INL (),pushed)` by
    simp[push_scope_with_var_def, return_def, Abbr `pushed`] >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  drule eval_for_cons_read >> disch_then (fn th => rewrite_tac[th]) >>
  simp[bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `runtime_consistent (extend_local env id ty F) cx pushed` by
    (irule typed_loop_push_runtime >> metis_tac[]) >>
  `popped_keys_indexed pushed.scopes` by
    metis_tac[push_scope_with_var_popped_keys_indexed] >>
  qpat_x_assum `!s t env ret env' st res st'.
                  push_scope_with_var _ _ _ _ = _ /\ _ ==> _`
    (drule_then assume_tac) >>
  drule_all (SRULE[ignore_bind_def] typed_loop_bracket_runtime) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `finally _ pop_scope pushed = (bracket_res,after)` >>
  `popped_keys_indexed after.scopes` by
    (qpat_x_assum `!s t env ret ty env_after st res st'. _` kall_tac >>
     qpat_x_assum `finally _ _ _ = _` mp_tac >>
     simp[finally_def, try_def, bind_def, ignore_bind_def, return_def,
          handle_loop_exception_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     gvs[COND_RATOR, return_def, raise_def, AllCaseEqs()] >>
     qpat_x_assum `!env ret env' st res st'. _` (drule_all_then assume_tac) >>
     irule pop_scope_popped_keys_indexed >>
     goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `broke` >- gvs[return_def] >>
  gvs[Abbr `bracket_res`, ignore_bind_def] >>
  qpat_x_assum `!s t env ret ty env_after st res st'. _`
    (drule_all_then assume_tac) >> simp[]
QED
Finalise eval_statement_loop_popped_keys_mutual

Theorem eval_statement_loop_popped_keys_indexed:
  (!cx s env ret_ty env' st res st'.
     type_stmt env ret_ty s = SOME env' /\
     runtime_consistent env cx st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     eval_stmt cx s st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!cx ss env ret_ty env' st res st'.
     type_stmts env ret_ty ss = SOME env' /\
     runtime_consistent env cx st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     eval_stmts cx ss st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes)
Proof
  metis_tac[cj 1 eval_statement_loop_popped_keys_mutual,
            cj 2 eval_statement_loop_popped_keys_mutual]
QED

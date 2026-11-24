(* Source preservation at the successful no-snapshot target cut. *)
Theory bodySavedTargetSourceMods
Ancestors
  bodySavedCallMutabilityMods bodySavedReadonlyCalleeMods bodySavedTargetWalkMods
  targetPureWalkTraversal targetPureWalkScopes targetPurePostTransport
  bodyPtrPopTargetFragTransport vyperMachineFrame vyperEvalFrame
  vyperCallOutcomeFrame vyperReadOnlyCalls vyperInterpreter vyperState
  exprLowering vyperTypeContract bodyCallSupport bodyInvSplit supportedProgram list pair
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

val machine_without_logs = irule state_rel_frame_machine >>
  conj_tac >- simp[machine_frame_def];

Triviality saved_checked_call_frame:
  contract_inv mods exps ctx cenv cx /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  source_body_call_supported cx (src,name) /\
  MEM (src,name) (linked_live_functions mods exps) /\
  ~call_can_mutate cenv (IntCall (src,name)) /\
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (eval_exprs cx actuals) ==>
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (eval_expr cx (Call ty (IntCall (src,name)) actuals fallback))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?tops. get_module_code cx src = SOME tops` by fs[source_body_call_supported_def] >>
  `?callable. lookup_callable_function cx.in_deploy name tops = SOME callable` by
    (qpat_x_assum `source_body_call_supported cx _` mp_tac >>
     Cases_on `src` >> simp[source_body_call_supported_def, PULL_EXISTS] >>
     rpt strip_tac >> gvs[] >>
     fs[supported_linked_callee_def, optionTheory.IS_SOME_EXISTS] >>
     rename1 `supported_function_decl _ _ _ = SOME decl` >>
     PairCases_on `decl` >>
     drule_then assume_tac supported_internal_lookup >>
     simp[lookup_callable_function_def]) >>
  PairCases_on `callable` >>
  rename1 `lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss)` >>
  drule_all_then assume_tac saved_selected_call_mutability_mods >>
  drule_all_then assume_tac saved_readonly_callee_frames_checked_mods >>
  qpat_x_assum `mut = View \/ mut = Pure` strip_assume_tac >> gvs[] >> (
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac walk_bind >>
  conj_tac >- (machine_without_logs >> simp[machine_frame_primitives]) >>
  gen_tac >>
  simp[Once lift_option_type_def, lift_option_def, bind_return] >>
  simp[Once lift_option_type_def, lift_option_def, bind_return] >>
  match_mp_tac walk_bind >>
  conj_tac >- (machine_without_logs >> simp[machine_frame_primitives]) >>
  gen_tac >> suspend "after_lookup")
QED

Resume saved_checked_call_frame[after_lookup]:
  markerLib.RESUME_TAC >> rpt strip_tac >> BETA_TAC >> (
  match_mp_tac walk_bind >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- (machine_without_logs >> simp[machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- (machine_without_logs >> match_mp_tac state_rel_frame_finally >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_primitives] >>
    match_mp_tac machine_frame_bind >> simp[machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> machine_without_logs >>
  match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_primitives] >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_primitives] >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- (Cases_on `nr` >> simp[machine_frame_primitives] >>
    Cases_on `cx.nonreentrant_slot` >> simp[machine_frame_primitives] >>
    match_mp_tac machine_frame_bind >>
    simp[machine_frame_view_lock, machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_push_function] >>
  rpt strip_tac >> fs[push_function_def, return_def] >>
  qpat_x_assum `cx with stk updated_by _ = _` (SUBST_ALL_TAC o SYM) >>
  match_mp_tac machine_frame_bind >>
  conj_tac >- (match_mp_tac state_rel_frame_finally_unless_halt >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_primitives] >>
    match_mp_tac state_rel_frame_finally >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_pop_function] >>
    match_mp_tac state_rel_frame_try >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_handlers] >>
    match_mp_tac machine_frame_bind >> simp[machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives])
QED
Finalise saved_checked_call_frame[local]

Theorem saved_target_source_update_mods:
  contract_inv mods exps ctx cenv cx /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := target_gas ++ tail) =
    (INL p,ee with gas_obs := tail)) /\
  read_result cx raw mid = (INL v,mid) ==>
  read_result cx raw ee = (INL v,ee) /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|>
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
       (eval_base_place cx bt)` by
    (irule saved_target_walk_from_calls_mods >>
     qexistsl [`\k. source_body_call_supported cx k /\
       MEM k (linked_live_functions mods exps)`, `cenv`] >>
     simp[EVERY_MEM] >> reverse conj_tac >- fs[EVERY_MEM] >>
     rpt gen_tac >> PairCases_on `key` >> strip_tac >>
     metis_tac[saved_checked_call_frame]) >>
  `eval_base_place cx bt (mid with gas_obs := target_gas) =
      (INL (PlaceR p),ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[eval_target_place_as_bind, bind_def] >>
     Cases_on `eval_base_place cx bt (mid with gas_obs := target_gas)` >> simp[] >>
     rename1 `eval_base_place _ _ _ = (base_result,base_state)` >>
     reverse (Cases_on `base_result`) >- simp[raise_def] >>
     rename1 `eval_base_place _ _ _ = (INL place_result,base_state)` >>
     Cases_on `place_result` >> simp[get_place_def, return_def, raise_def]) >>
  drule_all_then assume_tac target_walk_scopes >>
  qpat_x_assum `state_rel_frame _ (eval_base_place _ _)`
    (qspec_then `mid with gas_obs := target_gas` mp_tac o REWRITE_RULE [state_rel_frame_def]) >>
  simp[] >> strip_tac >>
  reverse conj_asm2_tac >- fs[machine_frame_def, evaluation_state_component_equality] >>
  qpat_assum `ee = _` (once_rewrite_tac o single) >>
  simp[SRULE [] target_saved_read_oracles]
QED

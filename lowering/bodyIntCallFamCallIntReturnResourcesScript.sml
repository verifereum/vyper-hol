(* Source invariant boundaries for the nested internal call return. *)
Theory bodyIntCallFamCallIntReturnResources
Ancestors
  bodyIntCallFamCallIntReturnFrame exprSimHypsDefs vyperPlaceWriteSoundness
  vyperTypeInvariants vyperEvalOutcomeSuffix exprOracleStorageInterfaces
  vyperCallOutcomeStorage list bodyIntCallSeamDefs
  bodyExprPreFacts vyperTypeStmtSoundness vyperInterpreter vyperState
  bodyIntCallSemanticEntry gasSummary vyperImmutableMetadataFrame
  vyperTypeStoragePreservation vyperStorageLayoutSafety vyperLookupStorage
  vyperStorageBackend bodyIntCallBodyTyping bodyIntCallSource
  bodySim supportedProgram vyperContext vyperTypeExprSoundness
  bodyIntCallJointContract

Theorem expr_sim_inv_source_frame:
  expr_sim_inv ce cx env es /\ ee.scopes = es.scopes /\
  immutable_metadata_frame es ee /\ state_well_typed ee /\
  accounts_well_typed ee.accounts /\ contract_storage_well_formed cx ee /\
  outcome_suffix es.outcomes ee.outcomes ==>
  expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `env_immutables_consistent env cx ee` by
    (irule env_immutables_consistent_metadata_frame >>
     fs[expr_sim_inv_def, env_consistent_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `oracle_storage_ok cx ee` by
    (irule oracle_storage_ok_suffix >> qexists `es` >>
     fs[expr_sim_inv_def]) >>
  gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
      outcomes_accounts_typed_def, outcome_suffix_def, EVERY_APPEND] >>
  metis_tac[]
QED

(* The handler changes only the result, not the dynamic source fields. *)
Theorem intcall_callee_src_dynamic:
  supported_program tops /\
  get_module_code (cx with stk updated_by CONS (NONE,name)) NONE = SOME tops /\
  supported_stmts tops bindings ss /\
  type_stmts env ret ss = SOME env' /\
  env_consistent env (cx with stk updated_by CONS (NONE,name)) es /\
  state_well_typed es /\ accounts_well_typed es.accounts /\
  context_well_typed (cx with stk updated_by CONS (NONE,name)) /\
  functions_well_typed (cx with stk updated_by CONS (NONE,name)) /\
  call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
    (int_calls_stmts ss) /\
  runtime_storage_consistent env (cx with stk updated_by CONS (NONE,name)) es /\
  IS_SOME es.outcomes /\
  oracle_storage_ok (cx with stk updated_by CONS (NONE,name)) es /\
  intcall_callee_src cx name ss es = (res,ee) ==>
  state_well_typed ee /\ accounts_well_typed ee.accounts /\
  contract_storage_well_formed (cx with stk updated_by CONS (NONE,name)) ee /\
  outcome_suffix es.outcomes ee.outcomes
Proof
  strip_tac >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss es` >>
  rename1 `eval_stmts _ _ _ = (result0,st)` >>
  `state_well_typed st /\ accounts_well_typed st.accounts` by
    (drule_all eval_stmts_preserves_state_and_accounts_well_typed >> simp[]) >>
  `contract_storage_well_formed (cx with stk updated_by CONS (NONE,name)) st` by
    (drule_all (cj 2 eval_stmts_storage_conjs) >> simp[]) >>
  `outcome_suffix es.outcomes st.outcomes` by
    (drule (cj 2 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `result0` >>
  gvs[intcall_callee_src_def, try_def, ignore_bind_def, bind_def, return_def] >>
  rename1 `handle_function ex st = _` >> Cases_on `ex` >>
  gvs[handle_function_def, return_def, raise_def]
QED

Theorem intcall_callee_marked_restore_inv:
  expr_sim_inv ce cx env (es with scopes := prev) /\
  (!gs result fin. intcall_callee_src cx name ss (es with gas_obs := gs) = (result,fin) ==>
    state_well_typed fin /\ accounts_well_typed fin.accounts /\
    contract_storage_well_formed (cx with stk updated_by CONS (NONE,name)) fin /\
    outcome_suffix es.outcomes fin.outcomes) /\
  gas_marked_exec memory (ctx,func) (intcall_callee_src cx name ss)
    (es,s) marks res ee r ==>
  expr_sim_inv ce cx env (ee with <|scopes := prev; gas_obs := []|>)
Proof
  strip_tac >>
  `immutable_metadata_frame es ee` by
    (drule_at Any marked_exec_immutable_metadata >>
     metis_tac[intcall_callee_src_metadata]) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule expr_sim_inv_source_frame >>
  reverse (rpt conj_tac)
  >- (qexists `es with scopes := prev` >>
      gvs[immutable_metadata_frame_def] >> metis_tac[]) >>
  fs[expr_sim_inv_def, state_well_typed_def,
     contract_storage_well_formed_def, well_formed_storage_def,
     storage_var_in_range_def, get_storage_backend_eq, oneline get_storage_def] >>
  metis_tac[]
QED

(* All semantic preconditions are obtained from the INVOKE boundary, rather
   than from the callee's value post. Gas observations carry no typing data. *)
Theorem intcall_entry_callee_dynamic:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,F,args,[],ret,ss) /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  intcall_entry tops ctx func ce cx env name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  intcall_callee_src cx name ss (es1 with gas_obs := gs) = (res,ee) ==>
  state_well_typed ee /\ accounts_well_typed ee.accounts /\
  contract_storage_well_formed (cx with stk updated_by CONS (NONE,name)) ee /\
  outcome_suffix es1.outcomes ee.outcomes
Proof
  strip_tac >>
  drule_all body_intcall_source_selection >> strip_tac >> gvs[] >>
  `cenv_module_pins tops ce` by metis_tac[body_inv_module_pins] >>
  drule intcall_entry_source >> strip_tac >>
  `stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
   expr_sim_inv ce cx env (es1 with scopes := prev) /\
   es1.scopes = [penv] /\
   call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
     (int_calls_stmts ss)` by fs[intcall_entry_def] >>
  `es1 with scopes := [penv] = es1` by
    simp[evaluation_state_component_equality] >>
  `?env_body env_after.
     type_stmts env_body ret ss = SOME env_after /\
     env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1 /\
     state_well_typed es1 /\ accounts_well_typed es1.accounts /\
     context_well_typed (cx with stk updated_by CONS (NONE,name)) /\
     functions_well_typed (cx with stk updated_by CONS (NONE,name)) /\
     contract_storage_well_formed (cx with stk updated_by CONS (NONE,name)) es1 /\
     storage_layout_safe (cx with stk updated_by CONS (NONE,name)) /\
     oracle_storage_ok (cx with stk updated_by CONS (NONE,name)) es1` by
    (fs[cenv_module_pins_def] >>
     drule_all pinned_internal_bound_body_typing >> strip_tac >>
     drule_all intcall_bound_source_invariants >>
     disch_then (qspec_then `name` strip_assume_tac) >>
     qexistsl [`env_body`,`env_after`] >>
     gvs[]) >>
  drule_at (Pat `intcall_callee_src _ _ _ _ = _`) intcall_callee_src_dynamic >>
  simp[] >> disch_then irule >>
  fs[supported_function_body_def, body_inv_def, expr_sim_inv_def,
     runtime_storage_consistent_def, runtime_consistent_def,
     get_module_code_def, oracle_storage_ok_outcomes, oracle_storage_ok_payload,
     contract_storage_well_formed_def, well_formed_storage_def,
     storage_var_in_range_def, get_storage_backend_eq, oneline get_storage_def] >>
  conj_tac
  >- (qexistsl [`env_after`,`env_body`,`ret`] >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at Any)
QED

Theorem intcall_entry_marked_restore_inv:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,F,args,[],ret,ss) /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  intcall_entry tops ctx func ce cx env name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  gas_marked_exec memory (ctx,callee) (intcall_callee_src cx name ss)
    (es1,entered) marks res ee r ==>
  expr_sim_inv ce cx env (ee with <|scopes := prev; gas_obs := []|>)
Proof
  strip_tac >>
  irule intcall_callee_marked_restore_inv >>
  goal_assum (drule_at Any) >>
  reverse conj_tac
  >- fs[intcall_entry_def] >>
  metis_tac[intcall_entry_callee_dynamic]
QED

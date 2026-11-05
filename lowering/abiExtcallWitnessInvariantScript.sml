(* Empty-storage boundaries for the concrete witness; no execution claims. *)
Theory abiExtcallWitnessInvariant
Ancestors
  abiExtcallWitnessRecords exprSimHypsDefs vyperStorageLayoutSafety
  vyperLookupStorage vyperTypeStoragePreservation vyperState vyperContext
  vyperInterpreter vfmState words relation vyperTypeCallStackSoundness
  vyperTypeCallGraphSoundness

Theorem witness_no_region:
  declared_storage_region witness_cx mid n subs = NONE
Proof
  simp[declared_storage_region_def, witness_module_code] >>
  Cases_on `mid` >> EVAL_TAC
QED

Theorem witness_no_storage_var:
  storage_var_info witness_cx mid n = NONE
Proof
  simp[storage_var_info_def, witness_module_code] >>
  Cases_on `mid` >> EVAL_TAC
QED

Theorem witness_storage_well_formed:
  contract_storage_well_formed witness_cx st
Proof
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def, witness_no_storage_var, witness_no_region]
QED

Theorem witness_layout_safe:
  storage_layout_safe witness_cx
Proof
  simp[storage_layout_safe_def, well_formed_layout_def,
       witness_no_storage_var, witness_no_region,
       nonreentrant_slot_separated_def, witness_cx_def,
       empty_evaluation_context_def]
QED

Theorem witness_oracle_storage:
  oracle_storage_ok witness_cx witness_es
Proof
  simp[oracle_storage_ok_def, witness_storage_well_formed,
       witness_es_def]
QED

Theorem witness_outcomes_typed:
  outcomes_accounts_typed witness_es.outcomes
Proof
  EVAL_TAC >> simp[dimword_def, empty_accounts_def, empty_account_state_def]
QED

Theorem witness_sim_inv:
  expr_sim_inv witness_cenv witness_cx witness_env witness_es
Proof
  simp[expr_sim_inv_def, witness_env_consistent, witness_state_typed,
       witness_accounts_typed, witness_context_typed, witness_functions_typed,
       witness_storage_well_formed, witness_layout_safe, witness_oracle_storage,
       witness_outcomes_typed, witness_tenv, witness_module_code,
       witness_cenv_def, witness_env_def, witness_es_def] >>
  EVAL_TAC >> simp[]
QED

Theorem witness_no_internal_calls:
  int_calls_expr witness_expr = []
Proof
  EVAL_TAC
QED

Theorem witness_expr_typed:
  well_typed_expr witness_env witness_expr
Proof
  EVAL_TAC >> simp[dimword_def]
QED


Theorem witness_empty_edges_tc[local]:
  !x y. TC (call_edge_rel []) x y ==> F
Proof
  ho_match_mp_tac TC_INDUCT >> simp[call_edge_rel_def]
QED

Theorem witness_calls_safe:
  call_evaluation_safe witness_cx []
Proof
  rewrite_tac[call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"probe")`, `[]`] >>
  simp[call_stack_follows_def, calls_follow_call_graph_def,
       irreflexive_def, witness_empty_edges_tc,
       functions_follow_call_graph_def, witness_module_code,
       witness_cx_def, empty_evaluation_context_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `lookup_callable_function _ _ [] = _` mp_tac >> EVAL_TAC
QED

Theorem witness_body_pre:
  expr_body_pre witness_cenv witness_cx witness_env witness_expr witness_es
Proof
  simp[expr_body_pre_def, witness_sim_inv, witness_expr_typed,
       witness_no_internal_calls, witness_calls_safe, witness_tenv, witness_tops] >>
  EVAL_TAC >> simp[dimword_def]
QED

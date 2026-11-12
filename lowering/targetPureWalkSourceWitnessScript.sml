Theory targetPureWalkSourceWitness
Ancestors
  targetPureWalkWitness targetPureWalkProbe targetPlaceSim targetPlaceSimCases exprSimMain exprSimHypsDefs
  vyperTypeInvariants

Theorem w_sim_inv:
  expr_sim_inv w_cenv w_cx w_env w_es
Proof
  simp[expr_sim_inv_def, w_cenv_def, w_cx_def, w_env_def, w_es_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] >>
  conj_tac >- (rewrite_tac[env_consistent_def] >> rpt conj_tac >> EVAL_TAC >> simp[vyperStateTheory.lookup_flag_def,
       vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def,
       wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]) >>
  conj_tac >- (EVAL_TAC >> simp[vyperTypingTheory.value_has_type_def,
    vyperTypingTheory.well_formed_type_value_def, vyperValueTheory.type_slot_size_def,
    wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]) >>
  conj_tac >- (simp[accounts_well_typed_def, vyperStateTheory.empty_state_def,
    account_well_typed_def, vfmStateTheory.lookup_account_def] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[context_well_typed_def,
    vyperContextTheory.empty_evaluation_context_def,
    vyperContextTheory.empty_call_txn_def] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (rewrite_tac[functions_well_typed_def] >> EVAL_TAC >>
    simp[vyperInterpreterTheory.lookup_function_def]) >>
  conj_tac >- (simp[vyperContextTheory.get_module_code_def,
    vyperContextTheory.empty_evaluation_context_def,
    vyperContextTheory.empty_call_txn_def] >> rpt strip_tac >>
    gvs[AllCaseEqs(), vyperStateTheory.lookup_flag_def]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `FLOOKUP _ _ = _` mp_tac >> EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[compileVyperTheory.build_compile_env_def,
    compileVyperTheory.build_flag_info_def, compileVyperTheory.allocate_args_def] >>
    rpt gen_tac >> AP_TERM_TAC >> AP_TERM_TAC >>
    AP_THM_TAC >> AP_TERM_TAC >> EVAL_TAC >> simp[]) >>
  rpt conj_tac >> EVAL_TAC >> simp[vyperStateTheory.lookup_flag_def,
    vyperStateTheory.find_var_decl_by_name_def, AllCaseEqs()]
QED

(* A singleton owner stack and the empty graph certify call safety. *)
Theorem w_calls_safe:
  call_evaluation_safe w_cx (int_calls_expr raw_log_index)
Proof
  rewrite_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"walk")`, `[]`] >>
  simp[w_cx_def, vyperTypeCallStackSoundnessTheory.call_stack_follows_def,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def,
       raw_log_index_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  conj_tac
  >- (simp[relationTheory.irreflexive_def,
           vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
           relationTheory.TC_DEF] >>
      qx_gen_tac `x` >> qexists_tac `\x y. F` >> simp[]) >>
  simp[vyperTypeCallStackSoundnessTheory.functions_follow_call_graph_def,
       vyperContextTheory.get_module_code_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[vyperInterpreterTheory.lookup_callable_function_def,
      vyperInterpreterTheory.lookup_function_def]
QED

Theorem raw_log_index_body_pre[local]:
  expr_sim_inv w_cenv w_cx env es ==>
  expr_body_pre w_cenv w_cx env raw_log_index es
Proof
  strip_tac >> rewrite_tac[expr_body_pre_def] >>
  simp[raw_log_index_typed, w_calls_safe] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem w_target_pre:
  target_pre w_cenv w_cx w_env w_bt w_es
Proof
  simp[target_pre_def, w_sim_inv, immutable_root_def, w_bt_def,
       target_root_def, target_indices_pre_def, raw_log_index_body_pre] >>
  EVAL_TAC
QED

Theorem w_target_sim:
  target_sim w_ctx w_func w_cenv w_cx w_env w_bt w_es
Proof
  irule (SRULE [target_case_def] target_case_all) >>
  simp[w_target_pre] >> qexists_tac `F` >> simp[] >>
  irule target_idx_case_ok >>
  simp[w_bt_def, targetPlaceLiveTheory.target_indices_def,
       raw_log_index_def, vyperTypeCallGraphTheory.int_calls_expr_def,
       cj 1 compile_expr_sim_mutual]
QED

Theorem w_target_typed:
  type_place_target w_env w_bt = SOME (Type (BaseT (UintT 256)))
Proof
  simp[w_bt_def, vyperTypeSystemTheory.well_typed_expr_def,
       raw_log_index_typed, w_env_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY, raw_log_index_def,
       vyperASTTheory.expr_type_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]
QED

Theorem w_source_pins:
  ~expr_can_mutate w_cenv (target_to_expr w_bt) /\
  w_cenv.ce_func_mutability = build_func_mutability (cx_tops w_cx) /\
  (!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops w_cx) ==>
    function_mutability_ok [(NONE, cx_tops w_cx)] vis mut nr dflts body) /\
  get_module_code w_cx NONE = SOME (cx_tops w_cx) /\
  EVERY (\c. FST c = NONE) (int_calls_target w_bt)
Proof
  EVAL_TAC >> simp[]
QED

Theorem w_gas_admissible:
  gas_admissible (eval_base_place w_cx w_bt) target_res_ok w_es
Proof
  rewrite_tac[gasContextTheory.gas_admissible_def] >>
  rpt gen_tac >>
  `eval_base_place w_cx w_bt (w_es with gas_obs := gs) =
    (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
     (w_es with gas_obs := gs) with logs :=
       (w_es with gas_obs := gs).logs ++
       [encode_raw_event_values w_cx.txn.target [] []])` by
    (rewrite_tac[w_bt_def] >> irule raw_log_target_execution >>
     simp[w_cx_def, w_es_def, vyperContextTheory.empty_evaluation_context_def,
          vyperContextTheory.empty_call_txn_def, vyperStateTheory.lookup_scopes_def,
          finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY]) >>
  simp[] >> rpt strip_tac >> gvs[targetPlaceSimDefsTheory.target_res_ok_def]
QED

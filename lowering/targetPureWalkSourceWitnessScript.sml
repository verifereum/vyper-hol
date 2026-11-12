Theory targetPureWalkSourceWitness
Ancestors
  targetPureWalkWitness targetPureWalkProbe targetPlaceSimCases exprSimMain exprSimHypsDefs
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

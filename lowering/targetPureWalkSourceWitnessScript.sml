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

(* The sufficient simulation producer requires a nonempty call stack,
   even when the expression contains no internal calls. *)
Theorem w_calls_not_safe:
  ~call_evaluation_safe w_cx (int_calls_expr raw_log_index)
Proof
  EVAL_TAC >> simp[]
QED

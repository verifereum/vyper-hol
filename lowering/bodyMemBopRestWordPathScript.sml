(* Allocation boundaries for the memory membership suffix. *)
Theory bodyMemBopRestWordPath
Ancestors
  fragGasMode allocaHistory venomMemProofs venomMemProps exprLoweringProps

Theorem rest_word_step_frontier:
  step_inst fuel ctx inst s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once venomExecSemanticsTheory.step_inst_def, AllCaseEqs()] >>
      mp_tac (Q.ISPEC `\s:venom_state. s.vs_alloca_next`
        venomInstProofs1Theory.bind_outputs_preserves) >>
      simp[venomStateTheory.update_var_def] >>
      disch_then drule >>
      Cases_on `ret.iret_adopt_fmp` >> simp[venomExecSemanticsTheory.merge_callee_state_def,
        venomExecSemanticsTheory.adopt_return_fmp_def, AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule venomMemPropsTheory.step_inst_alloca_alloca_next_mono >>
      simp[venomInstTheory.is_alloca_op_def]) >>
  `step_inst_base inst s = OK t` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_next,
    arithmeticTheory.LESS_EQ_REFL]
QED

Theorem rest_word_state_alloca_inv:
  stmt_state_rel ctx func cenv cx es s ==> alloca_inv s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def]
QED

Theorem rest_word_edge_alloca:
  gas_path_edge ctx fn s n (OK t) /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s ==>
  alloca_history fn t /\ alloca_inv t
Proof
  rw[fragGasPathTheory.gas_path_edge_def] >>
  gvs[fragExecTheory.exit_result_def] 
  >- metis_tac[allocaHistoryTheory.alloca_history_step]
  >- (drule_all venomMemProofsTheory.alloca_inv_step_inst_proof >>
      simp[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        venomMemDefsTheory.alloca_next_valid_def])
  >- (`alloca_history fn t'` by
        metis_tac[allocaHistoryTheory.alloca_history_step] >>
      irule history_phi_entry >> goal_assum (drule_at Any) >> simp[])
  >- (drule_all venomMemProofsTheory.alloca_inv_step_inst_proof >> strip_tac >>
      drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> strip_tac >>
      gvs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[])
  >- metis_tac[allocaHistoryTheory.alloca_history_step]
  >- metis_tac[venomMemProofsTheory.alloca_inv_step_inst_proof] >>
  qpat_x_assum `OK _ = _` (mp_tac o SYM) >>
  disch_then SUBST_ALL_TAC >> fs[fragExecTheory.exit_result_def]
QED

Theorem rest_word_path_alloca:
  !ctx fn s n r. gas_path ctx fn s n r ==>
  !t. r = OK t /\ fn_inst_ids_distinct fn /\
    alloca_history fn s /\ alloca_inv s ==>
    alloca_history fn t /\ alloca_inv t
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >> rpt strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  drule_all rest_word_edge_alloca >> strip_tac >> metis_tac[]
QED

Theorem rest_word_marked_alloca:
  gas_marked_path memory ctx fn s n (OK t) /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s ==>
  alloca_history fn t /\ alloca_inv t
Proof
  strip_tac >> drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
  drule rest_word_path_alloca >> simp[]
QED

Theorem rest_word_edge_frontier:
  gas_path_edge ctx fn s n (OK t) ==> s.vs_alloca_next <= t.vs_alloca_next
Proof
  rw[fragGasPathTheory.gas_path_edge_def] >>
  gvs[fragExecTheory.exit_result_def]
  >- metis_tac[rest_word_step_frontier]
  >- (drule rest_word_step_frontier >>
      drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> simp[])
  >- simp[venomStateTheory.jump_to_def] >>
  qpat_x_assum `OK _ = _` (mp_tac o SYM) >>
  disch_then SUBST_ALL_TAC >> fs[fragExecTheory.exit_result_def]
QED

Theorem rest_word_path_frontier:
  !ctx fn s n r. gas_path ctx fn s n r ==>
  !t. r = OK t ==> s.vs_alloca_next <= t.vs_alloca_next
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >> rpt strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  drule rest_word_edge_frontier >> simp[]
QED

Theorem rest_word_marked_allocation_posts:
  gas_marked_path memory ctx fn s n (OK t) /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s ==>
  alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule_all rest_word_marked_alloca >> strip_tac >> simp[] >>
  drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
  drule rest_word_path_frontier >> simp[]
QED

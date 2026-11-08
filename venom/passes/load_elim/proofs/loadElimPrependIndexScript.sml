Theory loadElimPrependIndex
Ancestors
  loadElimActualPhiFrame loadElimTargetWrites loadElimOccurrenceCoverage
  loadElimPaddedNoncall analysisSimDefs analysisSimProofsBase
  passSimulationProps venomExecProofs instIdxIndep
  list indexedLists rich_list venomInst loadElimDefs

Theorem le_actual_mapi_phi_length:
  le_configured_context ctx ==>
  phi_prefix_length
    (MAPi (\n i. load_elim_inst ctx actions (lats n) i) xs) =
  phi_prefix_length xs
Proof
  strip_tac >>
  `LENGTH (le_phi_prefix (MAPi (\n i. load_elim_inst ctx actions (lats n) i) xs)) =
   LENGTH (le_phi_prefix xs)` by simp[le_configured_transformed_phi_prefix] >>
  gvs[le_phi_prefix_take, LENGTH_TAKE, phi_prefix_length_le, arithmeticTheory.MIN_DEF]
QED

Theorem le_actual_prepend_phi_length:
  le_configured_context ctx ==>
  phi_prefix_length
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions =
  phi_prefix_length bb.bb_instructions + LENGTH (phis_for_block actions bb.bb_label)
Proof
  strip_tac >>
  drule le_actual_prepend_phi_prefix >>
  disch_then (qspecl_then [`result`, `bb`, `actions`] mp_tac) >>
  disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
  simp[le_phi_prefix_take, LENGTH_TAKE, phi_prefix_length_le, arithmeticTheory.MIN_DEF]
QED

Theorem le_actual_prepend_get_instruction:
  le_configured_context ctx /\ get_instruction bb n = SOME i /\
  phi_prefix_length bb.bb_instructions <= n ==>
  get_instruction
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb)
    (n + LENGTH (phis_for_block actions bb.bb_label)) =
  SOME (load_elim_inst ctx actions (df_at NONE result bb.bb_label n) i)
Proof
  strip_tac >>
  gvs[get_instruction_def] >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
       passSimulationPropsTheory.flat_mapi_singleton,
       le_actual_mapi_phi_length, LENGTH_TAKE, LENGTH_DROP,
       indexedListsTheory.LENGTH_MAPi, phi_prefix_length_le,
       arithmeticTheory.MIN_DEF, EL_APPEND_EQN, EL_DROP,
       indexedListsTheory.EL_MAPi]
QED

(* Rebase only successful continuations: INVOKE's terminal results belong
   to the callee and must not have their indices overwritten. *)
Theorem le_step_nonterm_rebase_OK:
  ~is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK u ==>
  step_inst fuel C inst (s with vs_inst_idx := n) =
    OK (u with vs_inst_idx := n) /\ u.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> conj_tac
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- simp[invoke_step_inst_idx_OK_only] >>
      simp[step_inst_idx_indep, exec_result_map_def]) >>
  metis_tac[venomExecSemanticsTheory.step_inst_preserves_inst_idx]
QED

Theorem le_step_term_rebase_OK:
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK u ==>
  step_inst fuel C inst (s with vs_inst_idx := n) = OK u /\
  u.vs_inst_idx = 0
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  gvs[venomExecSemanticsTheory.step_inst_def] >>
  `u.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
  simp[] >>
  drule terminator_step_inst_base_idx_norm0 >>
  disch_then (qspecl_then [`s`, `n`] mp_tac) >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := n)` >>
  simp[exec_result_map_def] >> strip_tac >>
  `v.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
  gvs[venomStateTheory.venom_state_component_equality]
QED

Theorem le_step_nonterm_from_zero:
  ~is_terminator inst.inst_opcode /\
  step_inst fuel C inst (s with vs_inst_idx := 0) = OK u ==>
  step_inst fuel C inst s = OK (u with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >> drule_all le_step_nonterm_rebase_OK >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem le_step_term_from_zero:
  is_terminator inst.inst_opcode /\
  step_inst fuel C inst (s with vs_inst_idx := 0) = OK u ==>
  step_inst fuel C inst s = OK u /\ u.vs_inst_idx = 0
Proof
  strip_tac >> drule_all le_step_term_rebase_OK >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED

(* exec_block advances from the input index, not the returned index. *)
Theorem le_body_increment_shift:
  t.vs_inst_idx = s.vs_inst_idx + g ==>
  (v with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx =
    (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx + g
Proof
  simp[]
QED

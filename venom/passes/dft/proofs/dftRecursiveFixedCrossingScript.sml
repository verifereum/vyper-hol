Theory dftRecursiveFixedCrossing
Ancestors
  dftRecursiveFixedPhase dftRecursiveFixedStep dftRecursiveActivePhase
  dftOccurrenceOrdinaryEdit dftOccurrenceResidual dftOccurrenceGasEdit
  dftOccurrenceReplay dftOccurrenceMachine dftOpenMachine dftOpenErase
  dftOriginalRuntime venomExecSemantics venomState list arithmetic

Theorem dft_fixed_invoke_failed_next[local]:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls n /\
  get_instruction bb s.vs_inst_idx = SOME call /\ call.inst_opcode = INVOKE /\
  dft_open_invoke C fn 1 bb call s (MAP (dft_fill_frame 1) ls) n =
    DftOpen (DftDone res) [] n ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone res) [] n; dft_occ_saved := []|>
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_erase_def, dft_occ_update_def]
QED

Theorem dft_fixed_crossing_operand_support[local]:
  decode_invoke call = SOME (nm,ops) /\
  EVERY (\p. ~MEM (Var (FST p)) call.inst_operands) us ==>
  EVERY (\p. ~MEM (Var (FST p)) ops) us
Proof
  simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  fs[EVERY_MEM] >> metis_tac[MEM]
QED

Theorem dft_fixed_crossing_failed[local]:
  dft_recursive_crossing_ready f b q pre x call post s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post q) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  LENGTH c.dft_occ_saved = LENGTH certs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) /\
  step_inst_base x s = OK t /\
  dft_open_invoke C fn 1 q call (t with vs_inst_idx := SUC s.vs_inst_idx)
    (MAP (dft_fill_frame 1) ls) nL = DftOpen (DftDone res) [] nL /\
  dft_open_invoke (dft_gas_edit_ctx q pre x call post C)
    (dft_gas_edit_fn q pre x call post fn) 1
    (dft_gas_edit_block q pre x call post q) call s
    (MAP (dft_fill_frame 1) rs) nR = DftOpen (DftDone res) [] nR ==>
  dft_fixed_phase q pre x call post (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >> drule dft_recursive_crossing_positions >> strip_tac >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dftRecursiveReturnPhaseTheory.dft_provenanced_frames_fill >> strip_tac >>
  drule_all dftRecursiveReturnPhaseTheory.dft_provenanced_frames_saved_empty >> strip_tac >>
  `x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\
   ~is_terminator x.inst_opcode` by
    (fs[dft_recursive_crossing_ready_def] >>
     drule_all dftOccurrenceFrameTheory.dft_invoke_inversion_disjoint >>
     Cases_on `x.inst_opcode = INVOKE` >>
     simp[venomEffectsTheory.read_effects_def,
          venomEffectsTheory.empty_effects_def, venomEffectsTheory.all_effects_def]) >>
  `dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen
       (DftAt fn 0 q (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL;
      dft_occ_saved := c.dft_occ_saved|>` by
    (drule_all dft_occ_ordinary_next >>
     disch_then (qspecl_then [`w`, `C`] mp_tac) >>
     Cases_on `ls` >> gvs[] >> simp[dft_occ_config_component_equality]) >>
  `call.inst_opcode = INVOKE` by fs[dft_recursive_crossing_ready_def] >>
  `dft_occ_oracle_next w C (dft_occ_oracle_next w C c) = c with
    <|dft_occ_core := DftOpen (DftDone res) [] nL; dft_occ_saved := []|>` by
    (qmatch_asmsub_abbrev_tac `dft_occ_oracle_next w C c = mid` >>
     `mid.dft_occ_core = DftOpen
       (DftAt fn 0 q (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL` by
       simp[Abbr `mid`] >>
     qpat_assum `mid.dft_occ_core = _`
       (mp_then Any mp_tac dft_fixed_invoke_failed_next) >>
     simp[] >> disch_then (qspec_then `w` mp_tac) >> simp[Abbr `mid`]) >>
  `dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d = d with
    <|dft_occ_core := DftOpen (DftDone res) [] nR; dft_occ_saved := []|>` by
    (drule_all dft_fixed_invoke_failed_next >> simp[]) >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w C) 2 c) /\
   dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
    metis_tac[dft_original_runtime_iter, dft_original_runtime_next] >>
  gvs[FUNPOW_2] >> simp[dft_fixed_phase_def, dft_fixed_control_def] >>
  qexists `[]` >> simp[]
QED

Theorem dft_fixed_crossing_next:
  dft_recursive_crossing_ready f b q pre x call post s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post q) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_phase q pre x call post (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >> drule dft_recursive_crossing_partner_success >> strip_tac >>
  drule_all dft_recursive_partner_updates >> strip_tac >>
  `dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s` by
    metis_tac[dft_recursive_pending_cut] >>
  `EVERY (\p. ~MEM (Var (FST p)) call.inst_operands) us` by
    (drule dft_recursive_partner_disjoint >> fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `t = dft_pending_apply us s` kall_tac >>
  Cases_on `decode_invoke call`
  >- (irule dft_fixed_crossing_failed >> simp[dft_open_invoke_def] >>
      metis_tac[]) >>
  rename1 `decode_invoke call = SOME pair` >> PairCases_on `pair` >>
  rename1 `decode_invoke call = SOME (nm,ops)` >>
  `eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = eval_operands ops s` by
    (irule dft_cut_pair_eval_operands >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[dft_fixed_crossing_operand_support]) >>
  Cases_on `lookup_function nm C.ctx_functions`
  >- (irule dft_fixed_crossing_failed >>
      simp[dft_open_invoke_def, dft_gas_edit_lookup_function] >>
      metis_tac[]) >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  Cases_on `eval_operands ops s`
  >- (irule dft_fixed_crossing_failed >>
      simp[dft_open_invoke_def, dft_gas_edit_lookup_function] >>
      metis_tac[]) >>
  rename1 `eval_operands ops s = SOME args` >>
  `setup_callee callee args (t with vs_inst_idx := SUC s.vs_inst_idx) =
   setup_callee callee args s` by metis_tac[dft_cut_pair_setup_callee] >>
  Cases_on `setup_callee callee args s`
  >- (irule dft_fixed_crossing_failed >>
      simp[dft_open_invoke_def, dft_gas_edit_lookup_function, dft_gas_edit_setup_callee] >>
      metis_tac[]) >>
  irule dft_fixed_crossing_enter >> simp[] >> metis_tac[]
QED

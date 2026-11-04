Theory dftOriginalSuccessor
Ancestors
  dftOriginalCutLifecycle dftOriginalScheduleRuntime dftProtectedRuntime
  dftOccurrenceAvailability venomWf venomInst venomExecProofs
  list rich_list sorting finite_map

Theorem dft_perm_front[local]:
  xs <> [] /\ ys <> [] /\ PERM xs ys /\ LAST xs = LAST ys ==>
  PERM (FRONT xs) (FRONT ys)
Proof
  strip_tac >>
  `xs = FRONT xs ++ [LAST xs] /\ ys = FRONT ys ++ [LAST ys]` by
    metis_tac[APPEND_FRONT_LAST] >>
  qpat_x_assum `PERM xs ys` mp_tac >>
  once_asm_rewrite_tac[] >> simp[PERM_APPEND_IFF, FRONT_APPEND]
QED

Theorem dft_wf_front_nonterm[local]:
  bb_well_formed b ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT b.bb_instructions)
Proof
  strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
  `~NULL b.bb_instructions` by (Cases_on `b.bb_instructions` >> fs[bb_well_formed_def]) >>
  `EL n (FRONT b.bb_instructions) = EL n b.bb_instructions` by simp[EL_FRONT] >>
  `n < LENGTH b.bb_instructions` by
    (Cases_on `b.bb_instructions` >> fs[LENGTH_FRONT]) >>
  `n = PRE (LENGTH b.bb_instructions)` by (fs[bb_well_formed_def] >> metis_tac[]) >>
  Cases_on `b.bb_instructions` >> fs[LENGTH_FRONT]
QED

Theorem dft_original_front_nonterm:
  dft_original_block f b q ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT q.bb_instructions)
Proof
  strip_tac >> drule dft_original_block_perm >> strip_tac >>
  `bb_well_formed b` by
    fs[dft_original_block_def, dft_original_schedule_def, wf_function_def] >>
  `PERM (FRONT q.bb_instructions) (FRONT b.bb_instructions)` by
    (irule dft_perm_front >> fs[dft_original_block_def, bb_well_formed_def]) >>
  drule PERM_EVERY >> metis_tac[dft_wf_front_nonterm]
QED

Theorem dft_original_terminator_last:
  dft_original_block f b q /\ get_instruction q s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode ==>
  s.vs_inst_idx = PRE (LENGTH q.bb_instructions) /\ inst = LAST q.bb_instructions
Proof
  strip_tac >> drule dft_original_front_nonterm >> strip_tac >>
  `s.vs_inst_idx < LENGTH q.bb_instructions /\
   inst = EL s.vs_inst_idx q.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `~NULL q.bb_instructions` by (Cases_on `q.bb_instructions` >> gvs[]) >>
  `s.vs_inst_idx = PRE (LENGTH q.bb_instructions)` by
    (fs[EVERY_EL] >> spose_not_then assume_tac >>
     `s.vs_inst_idx < LENGTH (FRONT q.bb_instructions)` by
       (Cases_on `q.bb_instructions` >> fs[LENGTH_FRONT]) >>
     metis_tac[EL_FRONT]) >>
  `q.bb_instructions <> []` by (Cases_on `q.bb_instructions` >> gvs[]) >>
  simp[] >> metis_tac[listTheory.LAST_EL]
QED

Theorem dft_original_cut_exit_outputs:
  dft_original_block f b q /\ dft_original_cut f b q s /\
  get_instruction q s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode ==>
  !d v. MEM d b.bb_instructions /\ MEM v d.inst_outputs ==>
    v IN FDOM s.vs_vars
Proof
  strip_tac >> drule_all dft_original_terminator_last >> strip_tac >>
  `MEM inst q.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `MEM inst b.bb_instructions` by metis_tac[dft_original_block_mem] >>
  `EVERY inst_wf b.bb_instructions` by
    fs[dft_original_cut_def, dft_original_schedule_def] >>
  `inst_wf inst` by fs[EVERY_MEM] >>
  `inst.inst_outputs = []` by metis_tac[terminator_no_outputs] >>
  rpt strip_tac >>
  `MEM d q.bb_instructions` by metis_tac[dft_original_block_mem] >>
  `?i. i < LENGTH q.bb_instructions /\ d = EL i q.bb_instructions` by
    metis_tac[MEM_EL] >>
  `i <> s.vs_inst_idx` by
    (strip_tac >> gvs[get_instruction_def, AllCaseEqs()]) >>
  `i < s.vs_inst_idx` by decide_tac >>
  `MEM d (TAKE s.vs_inst_idx q.bb_instructions)` by
    (simp[MEM_EL] >> qexists `i` >> simp[EL_TAKE, LENGTH_TAKE] >> decide_tac) >>
  fs[dft_original_cut_def, dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_original_occ_successor_available:
  dft_original_block f b q /\ dft_original_cut f b q s /\
  fn_reachable f s.vs_current_bb /\
  get_instruction q s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftEnter fn 0 t) stack' n'
  ==> fn_reachable f t.vs_current_bb /\ strict_dom_vars_defined f t
Proof
  strip_tac >> drule_all dft_occ_terminator_exit >> strip_tac >>
  `MEM inst q.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `MEM inst b.bb_instructions` by metis_tac[dft_original_block_mem] >>
  `EVERY inst_wf b.bb_instructions` by
    fs[dft_original_cut_def, dft_original_schedule_def] >>
  `inst_wf inst` by fs[EVERY_MEM] >>
  drule_all step_inst_base_term_succs >> strip_tac >>
  drule_all dft_original_terminator_last >> strip_tac >>
  `t.vs_vars = s.vs_vars` by metis_tac[dft_terminator_vars] >>
  `MEM t.vs_current_bb (bb_succs q)` by
    (Cases_on `q.bb_instructions` >> gvs[bb_succs_def]) >>
  `MEM t.vs_current_bb (bb_succs b)` by metis_tac[dft_original_block_succs] >>
  `fn_cfg_edge f s.vs_current_bb t.vs_current_bb` by
    (fs[dft_original_cut_def, dft_original_schedule_def,
        dft_activation_cut_def, fn_cfg_edge_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[fn_reachable_step] >>
  `!d v. MEM d b.bb_instructions /\ MEM v d.inst_outputs ==>
      v IN FDOM s.vs_vars` by metis_tac[dft_original_cut_exit_outputs] >>
  `ssa_form f /\ wf_function f` by
    fs[dft_original_cut_def, dft_original_schedule_def, wf_ssa_def] >>
  irule dftAvailabilityTheory.dft_dominance_transfer >> simp[] >>
  qexistsl_tac [`b`, `s`] >>
  fs[dft_original_cut_def, dft_original_schedule_def,
     dft_activation_cut_def, wf_ssa_def] >> metis_tac[]
QED

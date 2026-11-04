Theory dftOccurrenceOrdinaryStop
Ancestors
  dftOccurrenceOrdinaryEdit dftOccurrenceOrdinaryObserve dftOrdinaryStop dftOrdinarySwap
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecSemantics venomInst venomEffects dftScheduleOrder contextCodegenRel list arithmetic

Theorem dft_occ_ordinary_abort:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = Abort a t ==>
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) (MAP (dft_fill_frame 0) stack) n
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, dft_erase_def] >>
  `!f. dft_fill_frame 0 (dft_fill_frame 1 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem dft_occ_ordinary_second_abort_next:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  dft_ordinary_swap_pair x y /\ step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  (dft_occ_oracle_next w C (dft_occ_oracle_next w C c)).dft_occ_core =
    DftOpen (DftDone (Abort a t)) (MAP (dft_fill_frame 0) stack) n
Proof
  strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] SUBST1_TAC) >>
  qmatch_goalsub_abbrev_tac `(dft_occ_oracle_next w C c1).dft_occ_core` >>
  `c1.dft_occ_core = DftOpen
     (DftAt fn 0 bb (sx with vs_inst_idx := SUC s.vs_inst_idx))
     (MAP (dft_fill_frame 0) stack) n` by simp[Abbr `c1`] >>
  drule dft_occ_ordinary_abort >> simp[] >>
  disch_then kall_tac >>
  `!f. dft_fill_frame 0 (dft_fill_frame 0 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem dft_occ_abort_clear:
  c.dft_occ_core = DftOpen (DftDone (Abort a t)) stack n ==>
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) [] n
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_return_def, dft_erase_def]
QED

Theorem dft_occ_ordinary_first_abort:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb' s.vs_inst_idx = SOME y /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME x /\
  step_inst_base x s = Abort a t ==>
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) (MAP (dft_fill_frame 0) stack) n /\
  ?j u. 1 <= j /\ j <= 2 /\
    (FUNPOW (dft_occ_oracle_next w C') j d).dft_occ_core =
      DftOpen (DftDone (Abort a u)) (MAP (dft_fill_frame 0) stack') n'
Proof
  strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  conj_tac >- (irule dft_occ_ordinary_abort >> metis_tac[]) >>
  drule_all dft_ordinary_first_abort_crossing >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac)
  >- (qexistsl_tac [`1`, `u`] >> simp[FUNPOW_2, FUNPOW] >>
      irule dft_occ_ordinary_abort >> metis_tac[]) >>
  qexistsl_tac [`2`, `u`] >> simp[FUNPOW_2, FUNPOW] >>
  irule dft_occ_ordinary_second_abort_next >>
  metis_tac[dft_ordinary_swap_pair_sym]
QED

Theorem dft_occ_ordinary_second_abort:
  dft_ordinary_swap_pair x y /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  get_instruction bb' s.vs_inst_idx = SOME y /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) (MAP (dft_fill_frame 0) stack) n /\
  ?u. (dft_occ_oracle_next w C' d).dft_occ_core =
    DftOpen (DftDone (Abort a u)) (MAP (dft_fill_frame 0) stack') n'
Proof
  strip_tac >> conj_tac
  >- (simp[FUNPOW_2, FUNPOW] >> irule dft_occ_ordinary_second_abort_next >> metis_tac[]) >>
  drule_all dft_ordinary_second_abort_crossing >> strip_tac >>
  qexists_tac `u` >> irule dft_occ_ordinary_abort >>
  fs[dft_ordinary_swap_pair_def] >> metis_tac[]
QED

Theorem dft_ordinary_abort_crossing_ranges:
  dft_ordinary_swap_pair x y /\ inst_wf x /\
  ~dft_must_order x y /\ step_inst_base x s = Abort a t ==>
  inst_mem_ranges y u = []
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ x.inst_opcode <> INVOKE` by
    fs[dft_ordinary_swap_pair_def] >>
  `~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
     write_effects x.inst_opcode = empty_effects)` by fs[dft_must_order_def] >>
  drule_all dft_ordinary_nonroot_abort_class >> strip_tac >>
  irule dft_ordinary_no_memory_ranges >>
  fs[dft_must_order_def, write_effects_def, all_effects_def,
     pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_occ_ordinary_first_abort_observe:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ ~dft_must_order x y /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb' s.vs_inst_idx = SOME y /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME x /\
  step_inst_base x s = Abort a t /\ h < 2 /\
  dft_open_observe f i u (FUNPOW (dft_occ_oracle_next w C') h d).dft_occ_core /\
  inst_mem_ranges i u <> [] ==>
  f = fn' /\ i = x /\
  dft_open_observe fn i s c.dft_occ_core /\
  (!op. MEM op i.inst_operands ==> eval_operand op u = eval_operand op s) /\
  inst_mem_ranges i u = inst_mem_ranges i s /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  `h = 0 \/ h = 1` by decide_tac
  >- (gvs[FUNPOW, dft_open_observe_def] >>
      metis_tac[dft_ordinary_abort_crossing_ranges]) >>
  gvs[FUNPOW] >>
  `?sy. step_inst_base y s = OK sy /\
         u = sy with vs_inst_idx := SUC s.vs_inst_idx` by
    (irule dft_occ_ordinary_success_inv >>
     qpat_x_assum `dft_open_observe _ _ _ _` mp_tac >>
     simp[dft_open_observe_def] >> metis_tac[]) >>
  gvs[] >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C'`] assume_tac) >>
  gvs[dft_open_observe_def] >>
  drule_all dft_ordinary_observe_indexed >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) >> gvs[]
QED

Theorem dft_occ_ordinary_second_abort_observe:
  dft_ordinary_swap_pair x y /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  get_instruction bb' s.vs_inst_idx = SOME y /\
  step_inst_base x s = OK sx /\
  dft_open_observe f i u d.dft_occ_core /\ inst_mem_ranges i u <> [] ==>
  f = fn' /\ i = y /\ u = s /\
  dft_open_observe fn i (sx with vs_inst_idx := SUC s.vs_inst_idx)
    (dft_occ_oracle_next w C c).dft_occ_core /\
  (!op. MEM op i.inst_operands ==>
    eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op u) /\
  inst_mem_ranges i (sx with vs_inst_idx := SUC s.vs_inst_idx) = inst_mem_ranges i u /\
  sx.vs_memory = u.vs_memory
Proof
  strip_tac >> gvs[dft_open_observe_def] >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode` by fs[dft_ordinary_swap_pair_def] >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  `dft_ordinary_swap_pair i x` by metis_tac[dft_ordinary_swap_pair_sym] >>
  qpat_x_assum `dft_ordinary_swap_pair x i` kall_tac >>
  drule_all dft_ordinary_observe_indexed >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) >>
  gvs[dft_open_observe_def]
QED

Theorem dft_occ_abort_prefix_clear:
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) stack n ==>
  (FUNPOW (dft_occ_oracle_next w C) (SUC j) c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) [] n
Proof
  strip_tac >> rewrite_tac[FUNPOW_SUC] >>
  irule dft_occ_abort_clear >> metis_tac[]
QED

Theorem dft_occ_abort_bounded_clear:
  (?j t. 1 <= j /\ j <= 2 /\
    (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
      DftOpen (DftDone (Abort a t)) stack n) ==>
  ?k t. 2 <= k /\ k <= 3 /\
    (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
      DftOpen (DftDone (Abort a t)) [] n
Proof
  strip_tac >> qexistsl_tac [`SUC j`, `t`] >>
  simp[] >> irule dft_occ_abort_prefix_clear >> metis_tac[]
QED

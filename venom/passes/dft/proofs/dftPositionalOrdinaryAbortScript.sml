Theory dftPositionalOrdinaryAbort
Ancestors
  dftPositionalOrdinarySegment dftPositionalOrdinaryCrossing
  dftOccurrenceOrdinaryStop dftScheduleOrder
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomEffects
  list arithmetic

Theorem dft_occ_abort_tail:
  !k c. c.dft_occ_core = DftOpen (DftDone (Abort a t)) [] n ==>
    (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
      DftOpen (DftDone (Abort a t)) [] n
Proof
  Induct_on `k` >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_occ_abort_clear >> metis_tac[]
QED

Theorem dft_occ_abort_tail_no_observe:
  c.dft_occ_core = DftOpen (DftDone (Abort a t)) [] n ==>
  ~dft_open_observe f i s (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core
Proof
  strip_tac >> drule dft_occ_abort_tail >>
  disch_then (qspecl_then [`w`, `C`, `k`] assume_tac) >> simp[dft_open_observe_def]
QED

Theorem dft_ordinary_first_abort_directed_cover:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ ~dft_must_order x y /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  get_instruction b s.vs_inst_idx = SOME x /\
  get_instruction b' s.vs_inst_idx = SOME y /\
  get_instruction b' (SUC s.vs_inst_idx) = SOME x /\
  step_inst_base x s = Abort a t /\ 1 <= j /\ j <= 2 /\
  (FUNPOW (dft_occ_oracle_next w D) j d).dft_occ_core =
    DftOpen (DftDone (Abort a u)) stack n ==>
  dft_directed_prefix_cover w C D c d 2 (SUC j)
Proof
  strip_tac >> simp[dft_directed_prefix_cover_def] >> rpt strip_tac >>
  `k < 2` by
    (Cases_on `k < 2` >- simp[] >>
     `k = 2 /\ j = 2` by decide_tac >>
     gvs[dft_open_observe_def]) >>
  drule_all dft_occ_ordinary_first_abort_observe >>
  strip_tac >>
  qexistsl_tac [`0`, `f`, `i`, `s`] >> simp[FUNPOW, dft_open_observe_def]
QED

Theorem dft_ordinary_second_abort_directed_cover:
  dft_ordinary_swap_pair x y /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  get_instruction b s.vs_inst_idx = SOME x /\
  get_instruction b (SUC s.vs_inst_idx) = SOME y /\
  get_instruction b' s.vs_inst_idx = SOME y /\
  step_inst_base x s = OK sx /\
  (dft_occ_oracle_next w D d).dft_occ_core =
    DftOpen (DftDone (Abort a u)) stack n ==>
  dft_directed_prefix_cover w C D c d 3 2
Proof
  strip_tac >> simp[dft_directed_prefix_cover_def] >> rpt strip_tac >>
  `k = 0 \/ k = 1` by decide_tac
  >- (gvs[FUNPOW] >>
      `dft_open_observe g' i t d.dft_occ_core` by metis_tac[] >>
      drule_all dft_occ_ordinary_second_abort_observe >>
      disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
      qexistsl_tac [`1`, `f`, `i`, `sx with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[FUNPOW] >> metis_tac[]) >>
  gvs[FUNPOW, dft_open_observe_def]
QED

Theorem dft_ordinary_first_abort_segment:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  get_instruction b s.vs_inst_idx = SOME x /\
  get_instruction b' s.vs_inst_idx = SOME y /\
  get_instruction b' (SUC s.vs_inst_idx) = SOME x /\
  step_inst_base x s = Abort a t ==>
  ?q u. 2 <= q /\ q <= 3 /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_core =
      DftOpen (DftDone (Abort a t)) [] nL /\
    (FUNPOW (dft_occ_oracle_next w D) q d).dft_occ_core =
      DftOpen (DftDone (Abort a u)) [] nR /\
    dft_directed_prefix_cover w C D c d 2 q
Proof
  strip_tac >>
  `~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
      write_effects x.inst_opcode = empty_effects)` by fs[dft_must_order_def] >>
  drule_all dft_occ_ordinary_first_abort >>
  disch_then (qspecl_then [`w`, `D`, `C`] strip_assume_tac) >>
  qexistsl_tac [`SUC j`, `u`] >> simp[] >> conj_tac
  >- (simp[FUNPOW_2] >> irule dft_occ_abort_clear >> metis_tac[]) >>
  conj_tac
  >- (irule dft_occ_abort_prefix_clear >> metis_tac[]) >>
  irule dft_ordinary_first_abort_directed_cover >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem dft_ordinary_second_abort_segment:
  dft_ordinary_swap_pair x y /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  get_instruction b s.vs_inst_idx = SOME x /\
  get_instruction b (SUC s.vs_inst_idx) = SOME y /\
  get_instruction b' s.vs_inst_idx = SOME y /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  ?u. (FUNPOW (dft_occ_oracle_next w C) 3 c).dft_occ_core =
        DftOpen (DftDone (Abort a t)) [] nL /\
      (FUNPOW (dft_occ_oracle_next w D) 2 d).dft_occ_core =
        DftOpen (DftDone (Abort a u)) [] nR /\
      dft_directed_prefix_cover w C D c d 3 2
Proof
  strip_tac >> drule_all dft_occ_ordinary_second_abort >>
  disch_then (qspecl_then [`w`, `D`, `C`] strip_assume_tac) >>
  qexists `u` >> conj_tac
  >- (`3 = SUC 2` by simp[] >> pop_assum SUBST1_TAC >>
      irule dft_occ_abort_prefix_clear >> metis_tac[]) >>
  conj_tac
  >- (simp[FUNPOW_2] >> irule dft_occ_abort_clear >> metis_tac[]) >>
  irule dft_ordinary_second_abort_directed_cover >> conj_tac
  >- (goal_assum (drule_at Any)) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem dft_pos_ordinary_selected_first_abort_segment:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_slot C D fi bi f g b b' /\ s.vs_inst_idx = LENGTH pre /\
  step_inst_base x s = Abort a t ==>
  ?q u. 2 <= q /\ q <= 3 /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_core =
      DftOpen (DftDone (Abort a t)) [] nL /\
    (FUNPOW (dft_occ_oracle_next w D) q d).dft_occ_core =
      DftOpen (DftDone (Abort a u)) [] nR /\
    dft_directed_prefix_cover w C D c d 2 q
Proof
  strip_tac >>
  `get_instruction b s.vs_inst_idx = SOME x /\
   get_instruction b (SUC s.vs_inst_idx) = SOME y /\
   get_instruction b' s.vs_inst_idx = SOME y /\
   get_instruction b' (SUC s.vs_inst_idx) = SOME x` by
    (irule dft_pos_selected_fetch >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all dft_ordinary_first_abort_segment >> simp[]
QED

Theorem dft_pos_ordinary_selected_second_abort_segment:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_ordinary_swap_pair x y /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_slot C D fi bi f g b b' /\ s.vs_inst_idx = LENGTH pre /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  ?u. (FUNPOW (dft_occ_oracle_next w C) 3 c).dft_occ_core =
        DftOpen (DftDone (Abort a t)) [] nL /\
      (FUNPOW (dft_occ_oracle_next w D) 2 d).dft_occ_core =
        DftOpen (DftDone (Abort a u)) [] nR /\
      dft_directed_prefix_cover w C D c d 3 2
Proof
  strip_tac >>
  `get_instruction b s.vs_inst_idx = SOME x /\
   get_instruction b (SUC s.vs_inst_idx) = SOME y /\
   get_instruction b' s.vs_inst_idx = SOME y /\
   get_instruction b' (SUC s.vs_inst_idx) = SOME x` by
    (irule dft_pos_selected_fetch >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all dft_ordinary_second_abort_segment >> simp[]
QED

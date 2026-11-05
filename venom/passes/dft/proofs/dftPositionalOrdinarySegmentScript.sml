Theory dftPositionalOrdinarySegment
Ancestors
  dftPositionalOrdinaryCrossing dftOccurrenceOrdinaryObserve
  dftPositionalPhase dftOrdinarySwap dftOpenMachine dftOccurrenceMachine
  venomExecSemantics unitMemInv list arithmetic

Definition dft_directed_prefix_cover_def:
  dft_directed_prefix_cover w C D c d a b <=>
    !k g i t. k < b /\
      dft_open_observe g i t
        (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
      inst_mem_ranges i t <> [] ==>
      ?j f q s. j < a /\
        dft_open_observe f q s
          (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges q s
End

Theorem dft_ordinary_success_directed_cover:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  get_instruction b s.vs_inst_idx = SOME x /\
  get_instruction b (SUC s.vs_inst_idx) = SOME y /\
  get_instruction b' s.vs_inst_idx = SOME y /\
  get_instruction b' (SUC s.vs_inst_idx) = SOME x /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  dft_directed_prefix_cover w C D c d 2 2
Proof
  strip_tac >> drule_all dft_occ_ordinary_observe_source_prefix >>
  disch_then (qspecl_then [`w`, `D`, `C`] strip_assume_tac) >>
  simp[dft_directed_prefix_cover_def] >> rpt strip_tac >>
  `k = 0 \/ k = 1` by decide_tac
  >- (gvs[FUNPOW, dft_open_observe_def] >>
      qexistsl_tac [`1`, `f`, `i`, `sx with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[FUNPOW, dft_open_observe_def] >> metis_tac[]) >>
  gvs[FUNPOW, dft_open_observe_def] >>
  qexistsl_tac [`0`, `f`, `i`, `s`] >> simp[FUNPOW, dft_open_observe_def]
QED

Theorem dft_pos_ordinary_selected_success_cover:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  dft_pos_phase C D fi bi pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_slot C D fi bi f g b b' /\ s.vs_inst_idx = LENGTH pre /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  dft_directed_prefix_cover w C D c d 2 2
Proof
  strip_tac >>
  `get_instruction b s.vs_inst_idx = SOME x /\
   get_instruction b (SUC s.vs_inst_idx) = SOME y /\
   get_instruction b' s.vs_inst_idx = SOME y /\
   get_instruction b' (SUC s.vs_inst_idx) = SOME x` by
    (irule dft_pos_selected_fetch >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all dft_ordinary_success_directed_cover >> simp[]
QED

Theorem dft_pos_ordinary_selected_success_segment:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  dft_pos_phase C D fi bi pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_slot C D fi bi f g b b' /\ s.vs_inst_idx = LENGTH pre /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  dft_pos_phase C D fi bi pre x y post
    (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (FUNPOW (dft_occ_oracle_next w D) 2 d) /\
  dft_directed_prefix_cover w C D c d 2 2
Proof
  strip_tac >> conj_tac
  >- (drule_all dft_pos_ordinary_selected_success >> simp[]) >>
  drule_all dft_pos_ordinary_selected_success_cover >> simp[]
QED

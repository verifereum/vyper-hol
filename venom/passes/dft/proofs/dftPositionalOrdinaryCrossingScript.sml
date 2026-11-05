Theory dftPositionalOrdinaryCrossing
Ancestors
  dftPositionalOrdinaryBoundary dftOccurrenceOrdinaryEdit dftPositionalReturn
  dftPositionalPhase dftPositionalRuntime dftPositionalEdit dftOriginalRuntime
  dftOriginalScheduleRuntime dftOccurrenceReplay dftOccurrenceMachine
  dftOrdinarySwap venomExecSemantics venomInst list arithmetic

Theorem dft_pos_selected_instruction_lists:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_slot C D fi bi f g b b' ==>
  b.bb_instructions = pre ++ [x;y] ++ post /\
  b'.bb_instructions = pre ++ [y;x] ++ post
Proof
  rw[dft_pos_runtime_ready_def, dft_pos_slot_def] >>
  simp[dft_pos_edit_ctx_selected, dft_pos_edit_fn_selected]
QED

Theorem dft_pos_selected_fetch:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_slot C D fi bi f g b b' /\ i = LENGTH pre ==>
  get_instruction b i = SOME x /\
  get_instruction b (SUC i) = SOME y /\
  get_instruction b' i = SOME y /\
  get_instruction b' (SUC i) = SOME x
Proof
  strip_tac >> drule_all dft_pos_selected_instruction_lists >> strip_tac >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem dft_original_ready_twice:
  dft_original_context Corig C /\ dft_original_ready c ==>
  dft_original_ready (FUNPOW (dft_occ_oracle_next w C) 2 c)
Proof
  simp[FUNPOW_2] >> metis_tac[dft_original_runtime_next]
QED

Theorem dft_pos_phase_ordinary_advance[local]:
  dft_pos_phase C D fi bi pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_slot C D fi bi f g b b' /\ t.vs_inst_idx <> SUC (LENGTH pre) /\
  c' = c with <|dft_occ_core := DftOpen (DftAt f 0 b t)
      (MAP (dft_fill_frame 0) ls) nL;
      dft_occ_saved := if ls = [] then [] else c.dft_occ_saved|> /\
  d' = d with <|dft_occ_core := DftOpen (DftAt g 0 b' t)
      (MAP (dft_fill_frame 0) rs) nR;
      dft_occ_saved := if rs = [] then [] else d.dft_occ_saved|> /\
  dft_original_ready c' /\ dft_original_ready d' ==>
  dft_pos_phase C D fi bi pre x y post c' d'
Proof
  strip_tac >>
  `?certs. dft_pos_stack C D fi bi pre x y post certs ls rs /\
    LENGTH c.dft_occ_saved = LENGTH certs` by
    (fs[dft_pos_phase_def] >> metis_tac[]) >>
  drule dft_pos_stack_fill >> strip_tac >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  fs[dft_pos_phase_def] >>
  gvs[] >> simp[dft_pos_phase_def, dft_pos_control_def] >>
  qexists `certs` >> simp[] >> metis_tac[]
QED

Theorem dft_pos_ordinary_selected_success:
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
    (FUNPOW (dft_occ_oracle_next w D) 2 d)
Proof
  strip_tac >>
  `get_instruction b s.vs_inst_idx = SOME x /\
   get_instruction b (SUC s.vs_inst_idx) = SOME y /\
   get_instruction b' s.vs_inst_idx = SOME y /\
   get_instruction b' (SUC s.vs_inst_idx) = SOME x` by
    (irule dft_pos_selected_fetch >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w C) 2 c) /\
   dft_original_ready (FUNPOW (dft_occ_oracle_next w D) 2 d)` by
    (fs[dft_pos_phase_def] >> metis_tac[dft_original_ready_twice]) >>
  drule_all dft_occ_ordinary_swap_ok >>
  disch_then (qspecl_then [`w`, `D`, `C`] strip_assume_tac) >>
  `(sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)).vs_inst_idx <>
     SUC (LENGTH pre)` by simp[] >>
  irule dft_pos_phase_ordinary_advance >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`b`, `b'`, `c`, `d`] >>
  simp[FUNPOW_2, NoAsms] >> metis_tac[]
QED

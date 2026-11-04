Theory dftOccurrenceOrdinaryEdit
Ancestors
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  dftOrdinarySwap venomExecSemantics venomInst list

Theorem dft_occ_ordinary_next:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  dft_occ_oracle_next w C c = c with
    <| dft_occ_core := DftOpen
         (DftAt fn 0 bb (t with vs_inst_idx := SUC s.vs_inst_idx))
         (MAP (dft_fill_frame 0) stack) n;
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
    MAP_MAP_o, combinTheory.o_DEF] >>
  `!f. dft_fill_frame 0 (dft_fill_frame 1 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[] >> Cases_on `stack` >> simp[dft_occ_update_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem dft_occ_ordinary_next_twice:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME a /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME b /\
  a.inst_opcode <> GAS /\ a.inst_opcode <> INVOKE /\
  b.inst_opcode <> GAS /\ b.inst_opcode <> INVOKE /\
  ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
  step_inst_base a s = OK sa /\
  step_inst_base b (sa with vs_inst_idx := SUC s.vs_inst_idx) = OK sab ==>
  dft_occ_oracle_next w C (dft_occ_oracle_next w C c) = c with
    <| dft_occ_core := DftOpen
         (DftAt fn 0 bb (sab with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
         (MAP (dft_fill_frame 0) stack) n;
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>
Proof
  strip_tac >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] SUBST1_TAC) >>
  qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C c1` >>
  `c1.dft_occ_core = DftOpen
     (DftAt fn 0 bb (sa with vs_inst_idx := SUC s.vs_inst_idx))
     (MAP (dft_fill_frame 0) stack) n` by simp[Abbr `c1`] >>
  drule dft_occ_ordinary_next >> simp[] >>
  disch_then kall_tac >> simp[Abbr `c1`] >>
  `!f. dft_fill_frame 0 (dft_fill_frame 0 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem dft_occ_ordinary_swap_ok:
  dft_ordinary_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME a /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME b /\
  get_instruction bb' s.vs_inst_idx = SOME b /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME a /\
  step_inst_base a s = OK sa /\
  step_inst_base b (sa with vs_inst_idx := SUC s.vs_inst_idx) = OK sab ==>
  ?sb sba.
    step_inst_base b s = OK sb /\
    step_inst_base a (sb with vs_inst_idx := SUC s.vs_inst_idx) = OK sba /\
    (sab with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (sba with vs_inst_idx := SUC (SUC s.vs_inst_idx)) /\
    dft_occ_oracle_next w C (dft_occ_oracle_next w C c) = c with
      <| dft_occ_core := DftOpen
           (DftAt fn 0 bb (sab with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
           (MAP (dft_fill_frame 0) stack) n;
         dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |> /\
    dft_occ_oracle_next w C' (dft_occ_oracle_next w C' d) = d with
      <| dft_occ_core := DftOpen
           (DftAt fn' 0 bb' (sab with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
           (MAP (dft_fill_frame 0) stack') n';
         dft_occ_saved := if stack' = [] then [] else d.dft_occ_saved |>
Proof
  strip_tac >>
  `a.inst_opcode <> GAS /\ a.inst_opcode <> INVOKE /\
   b.inst_opcode <> GAS /\ b.inst_opcode <> INVOKE /\
   ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  `step_inst 0 C a s = OK sa /\
   step_inst 0 C b (sa with vs_inst_idx := SUC s.vs_inst_idx) = OK sab` by
    simp[step_inst_non_invoke] >>
  drule_all dft_ordinary_indexed_step_swap_ok >>
  simp[step_inst_non_invoke] >> strip_tac >>
  qexistsl_tac [`sb`, `sba`] >>
  simp[IgnAsm `(_ with vs_inst_idx := _) = (_ with vs_inst_idx := _)`] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (irule dft_occ_ordinary_next_twice >> metis_tac[]) >>
  qpat_x_assum `(_ with vs_inst_idx := _) = (_ with vs_inst_idx := _)`
    (fn th => rewrite_tac[th]) >>
  irule dft_occ_ordinary_next_twice >> simp[] >> metis_tac[]
QED

Theorem dft_occ_ordinary_success_inv:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftAt fn' budget bb' t) stack' n' ==>
  ?r. step_inst_base inst s = OK r /\
      t = r with vs_inst_idx := SUC s.vs_inst_idx
Proof
  strip_tac >>
  qpat_x_assum `(dft_occ_oracle_next _ _ _).dft_occ_core = _` mp_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, dft_erase_def] >>
  Cases_on `step_inst_base inst s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_erase_def]
QED

Theorem dft_occ_ordinary_swap_continue:
  dft_ordinary_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME a /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME b /\
  get_instruction bb' s.vs_inst_idx = SOME b /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME a /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftAt fn 0 bb t1) st1 n /\
  (dft_occ_oracle_next w C (dft_occ_oracle_next w C c)).dft_occ_core =
    DftOpen (DftAt fn 0 bb t2) st2 n ==>
  dft_occ_oracle_next w C' (dft_occ_oracle_next w C' d) = d with
    <| dft_occ_core := DftOpen (DftAt fn' 0 bb' t2)
         (MAP (dft_fill_frame 0) stack') n';
       dft_occ_saved := if stack' = [] then [] else d.dft_occ_saved |>
Proof
  strip_tac >>
  `a.inst_opcode <> GAS /\ a.inst_opcode <> INVOKE /\
   b.inst_opcode <> GAS /\ b.inst_opcode <> INVOKE /\
   ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  `?sa. step_inst_base a s = OK sa /\
        t1 = sa with vs_inst_idx := SUC s.vs_inst_idx` by
    (irule dft_occ_ordinary_success_inv >> metis_tac[]) >>
  `?sab. step_inst_base b t1 = OK sab /\
         t2 = sab with vs_inst_idx := SUC t1.vs_inst_idx` by
    (irule dft_occ_ordinary_success_inv >> simp[] >> metis_tac[]) >>
  gvs[] >> drule_all dft_occ_ordinary_swap_ok >>
  disch_then (qspecl_then [`w`, `C'`, `C`] strip_assume_tac) >> simp[]
QED

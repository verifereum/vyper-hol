Theory dftFlipOccurrence
Ancestors
  dftFlipOccurrenceProbe dftOrbitObservation dftOpenErase dftFlipRuntime
  dftRelationalEdit dftOccurrenceMachine dftOccurrenceReplay dftStructural arithmetic list option

Theorem dft_rel_frame_fill[local]:
  dft_rel_frame R br f g ==>
  dft_rel_frame R br (dft_fill_frame k f) (dft_fill_frame k g)
Proof
  Cases_on `f` >> Cases_on `g` >>
  simp[dft_rel_frame_def, dft_fill_frame_def]
QED

Theorem dft_rel_core_fill:
  dft_rel_core R br q r ==>
  dft_rel_core R br (dft_fill k q) (dft_fill k r)
Proof
  Cases_on `q` >> Cases_on `r` >>
  rename1 `dft_rel_core R br (DftOpen ctl stk n) (DftOpen ctl' stk' n')` >>
  Cases_on `ctl` >> Cases_on `ctl'` >>
  simp[dft_rel_core_def, dft_rel_control_def, dft_fill_def,
    dft_fill_control_def] >> rpt strip_tac >>
  gvs[LIST_REL_MAP] >>
  irule LIST_REL_mono >>
  qexists_tac `dft_rel_frame R br` >> simp[dft_rel_frame_fill]
QED

Theorem dft_rel_core_next_inf:
  dft_rel_interface C D R br /\
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_rel_core R br q r ==>
  dft_rel_core R br (dft_next_inf a C q) (dft_next_inf a D r)
Proof
  strip_tac >> simp[dft_next_inf_def, dft_erase_def] >>
  irule dft_rel_core_fill >> irule dft_flip_next >>
  simp[dft_rel_core_fill] >> metis_tac[]
QED

Theorem dft_flip_occ_update:
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d /\ dft_rel_core R br q r ==>
  dft_flip_occ_rel R br
    ((dft_occ_update c q) with dft_occ_core := q)
    ((dft_occ_update d r) with dft_occ_core := r)
Proof
  Cases_on `c.dft_occ_core` >> Cases_on `d.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stk n` >>
  rename1 `d.dft_occ_core = DftOpen ctl' stk' n'` >>
  Cases_on `q` >> Cases_on `r` >>
  rename1 `dft_rel_core R br (DftOpen next frames m) (DftOpen next' frames' m')` >>
  Cases_on `ctl` >> Cases_on `ctl'` >>
  Cases_on `next` >> Cases_on `next'` >>
  simp[dft_flip_occ_rel_def, dft_rel_core_def, dft_rel_control_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `frames` >> Cases_on `frames'` >>
  gvs[dft_occ_update_def, dft_flip_occ_rel_def, dft_rel_core_def] >>
  Cases_on `d.dft_occ_saved` >> simp[] >>
  TRY (rename1 `d.dft_occ_saved = pair::saved` >> PairCases_on `pair` >> simp[]) >>
  `LIST_REL flip_rel b.bb_instructions b'.bb_instructions` by metis_tac[] >>
    drule dft_flip_get_instruction >>
    disch_then (qspec_then `v.vs_inst_idx` mp_tac) >>
    Cases_on `get_instruction b v.vs_inst_idx` >>
    Cases_on `get_instruction b' v.vs_inst_idx` >> simp[] >>
    strip_tac >> drule dft_flip_tests >> strip_tac >>
    `x.inst_id = x'.inst_id` by
      metis_tac[flip_rel_def, flip_operands_inst_id] >>
    gvs[] >> Cases_on `x'.inst_opcode = INVOKE` >> simp[]
QED

Theorem dft_flip_occ_next:
  dft_rel_interface C D R br /\
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d ==>
  dft_flip_occ_rel R br (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w D d)
Proof
  strip_tac >>
  `dft_occ_address c = dft_occ_address d` by
    (irule dft_flip_occ_address >> metis_tac[]) >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def] >>
  irule dft_flip_occ_update >> simp[] >> conj_tac
  >- metis_tac[] >>
  irule dft_rel_core_next_inf >>
  gvs[dft_flip_occ_rel_def] >> metis_tac[]
QED

Theorem dft_flip_occ_iter:
  !j c d. dft_rel_interface C D R br /\
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d ==>
  dft_flip_occ_rel R br (FUNPOW (dft_occ_oracle_next w C) j c)
    (FUNPOW (dft_occ_oracle_next w D) j d)
Proof
  Induct_on `j` >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_flip_occ_next >> metis_tac[]
QED

Theorem dft_flip_occ_observation:
  dft_rel_interface C D R br /\
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d ==>
  dft_orbit_observation w C D c d
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >>
      `dft_flip_occ_rel R br (FUNPOW (dft_occ_oracle_next w C) j c)
        (FUNPOW (dft_occ_oracle_next w D) j d)` by
        (irule dft_flip_occ_iter >> metis_tac[]) >>
      drule_all dft_flip_occ_terminal >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >>
  `dft_flip_occ_rel R br (FUNPOW (dft_occ_oracle_next w C) k c)
    (FUNPOW (dft_occ_oracle_next w D) k d)` by
    (irule dft_flip_occ_iter >> metis_tac[]) >>
  drule_all dft_flip_occ_memory_backward >> metis_tac[]
QED

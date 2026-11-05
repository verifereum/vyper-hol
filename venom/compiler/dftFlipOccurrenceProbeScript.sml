Theory dftFlipOccurrenceProbe
Ancestors
  dftFlipRuntime dftStructural dftNormalizedEndpoint dftOccurrenceReplay dftRelationalEdit
  dftOccurrenceMachine dftOpenMachine unitMemInv contextCodegenRel codegenRel
  dftDefs passSharedDefs venomEffects list option

Definition dft_flip_occ_rel_def:
  dft_flip_occ_rel R br c d <=>
    dft_rel_core R br c.dft_occ_core d.dft_occ_core /\
    c.dft_occ_path = d.dft_occ_path /\
    c.dft_occ_visit = d.dft_occ_visit /\
    c.dft_occ_saved = d.dft_occ_saved
End

Theorem dft_flip_occ_address:
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d ==>
  dft_occ_address c = dft_occ_address d
Proof
  Cases_on `c.dft_occ_core` >> Cases_on `d.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stk n` >>
  rename1 `d.dft_occ_core = DftOpen ctl' stk' n'` >>
  Cases_on `ctl` >> Cases_on `ctl'` >>
  simp[dft_flip_occ_rel_def, dft_rel_core_def, dft_rel_control_def,
    dft_occ_address_def] >> rpt strip_tac >> gvs[] >>
  `LIST_REL flip_rel b.bb_instructions b'.bb_instructions` by metis_tac[] >>
  drule dft_flip_get_instruction >>
  disch_then (qspec_then `v.vs_inst_idx` mp_tac) >>
  Cases_on `get_instruction b v.vs_inst_idx` >>
  Cases_on `get_instruction b' v.vs_inst_idx` >> simp[] >>
  strip_tac >> gvs[flip_rel_def] >> metis_tac[flip_operands_inst_id]
QED

Theorem dft_flip_flippable_ranges:
  is_flippable i.inst_opcode ==> inst_mem_ranges i s = []
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def,
    inst_mem_ranges_def, source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem dft_flip_memory_instruction:
  flip_rel i j /\ inst_mem_ranges j s <> [] ==> j = i
Proof
  strip_tac >> gvs[flip_rel_def] >>
  `is_flippable (flip_operands i).inst_opcode` by
    (Cases_on `i.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def] >>
     Cases_on `i.inst_operands` >>
     gvs[flip_operands_def, is_flippable_def, is_commutative_def, is_comparator_def] >>
     Cases_on `t` >>
     gvs[flip_operands_def, is_flippable_def, is_commutative_def, is_comparator_def] >>
     Cases_on `t'` >> gvs[flip_operands_def, flip_comparison_opcode_def,
       is_flippable_def, is_commutative_def, is_comparator_def]) >>
  metis_tac[dft_flip_flippable_ranges]
QED

Theorem dft_flip_occ_memory_backward:
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d /\
  dft_open_observe g i t d.dft_occ_core /\ inst_mem_ranges i t <> [] ==>
  ?f. R f g /\ dft_open_observe f i t c.dft_occ_core
Proof
  simp[dft_open_observe_def, dft_flip_occ_rel_def] >> rpt strip_tac >>
  Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stk nL` >> Cases_on `ctl` >>
  gvs[dft_rel_core_def, dft_rel_control_def] >>
  `LIST_REL flip_rel b.bb_instructions bb.bb_instructions` by metis_tac[] >>
  drule dft_flip_get_instruction >>
  disch_then (qspec_then `t.vs_inst_idx` mp_tac) >>
  Cases_on `get_instruction b t.vs_inst_idx` >> simp[] >> strip_tac >>
  `i = x` by metis_tac[dft_flip_memory_instruction] >> gvs[] >> metis_tac[]
QED

Theorem dft_flip_occ_terminal:
  dft_flip_occ_rel R br c d /\
  c.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  d.dft_occ_core = DftOpen (DftDone rr) [] n
Proof
  simp[dft_flip_occ_rel_def] >> rpt strip_tac >>
  Cases_on `d.dft_occ_core` >>
  rename1 `d.dft_occ_core = DftOpen ctl stk m` >>
  Cases_on `ctl` >> gvs[dft_rel_core_def, dft_rel_control_def]
QED

Theorem dft_flip_occ_common_selection:
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_flip_occ_rel R br c d ==>
  dft_occ_oracle_next w D d =
    dft_occ_next (\n. w (dft_occ_address c)) D d
Proof
  strip_tac >> drule_all dft_flip_occ_address >>
  simp[dft_occ_oracle_next_def]
QED

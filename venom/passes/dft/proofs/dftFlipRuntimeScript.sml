Theory dftFlipRuntime
Ancestors
  dftScheduleReconstruction dftRelationalEdit dftPermSim dftScheduleOrder
  dftOriginalScheduleRuntime dftDefs dftStructural dftOpenMachine
  venomInst venomExecSemantics venomEffects passSharedDefs list sorting

Definition flip_rel_def:
  flip_rel i j <=> j = i \/ (is_flippable i.inst_opcode /\ j = flip_operands i)
End

Theorem dft_flip_from_block:
  ALL_DISTINCT (MAP (\i. i.inst_id) orig) /\ MEM i orig /\
  from_block orig j /\ i.inst_id = j.inst_id ==> flip_rel i j
Proof
  simp[from_block_def] >> rpt strip_tac >>
  `i = j'` by metis_tac[dft_reconstruction_unique_id, flip_operands_inst_id] >>
  gvs[flip_rel_def]
QED

Theorem dft_flip_provenance:
  dft_block_rel b dest ==>
  EVERY (\j. MEM j b.bb_instructions \/ from_block b.bb_instructions j)
    dest.bb_instructions
Proof
  simp[dft_block_rel_def] >> rpt strip_tac >>
  simp[EVERY_APPEND, EVERY_MEM, MEM_FILTER] >> metis_tac[EVERY_MEM]
QED

Theorem dft_flip_upgrade_element[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) orig) /\ MEM i orig /\
  (MEM j orig \/ from_block orig j) /\ (j = i \/ j = flip_operands i) ==>
  flip_rel i j
Proof
  rpt strip_tac
  >- simp[flip_rel_def]
  >- (`i = j` by metis_tac[dft_reconstruction_unique_id, flip_operands_inst_id] >>
      metis_tac[flip_rel_def])
  >- simp[flip_rel_def] >>
  irule dft_flip_from_block >> simp[flip_operands_inst_id] >>
  qexists `orig` >> metis_tac[]
QED

Theorem dft_flip_upgrade:
  !xs ys. ALL_DISTINCT (MAP (\i. i.inst_id) orig) /\
  EVERY (\i. MEM i orig) xs /\
  EVERY (\j. MEM j orig \/ from_block orig j) ys /\
  LIST_REL (\i j. j = i \/ j = flip_operands i) xs ys ==>
  LIST_REL flip_rel xs ys
Proof
  Induct >> rpt gen_tac >> Cases_on `ys` >> simp[] >>
  metis_tac[dft_flip_upgrade_element]
QED

Theorem dft_block_rel_guarded_reconstruction:
  dft_original_block f b b /\
  ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions) /\
  dft_block_rel b dest ==>
  ?mid. dft_original_block f b mid /\ mid.bb_label = dest.bb_label /\
    LIST_REL flip_rel mid.bb_instructions dest.bb_instructions
Proof
  strip_tac >> drule_all dft_block_rel_reconstruction >> strip_tac >>
  qexists `mid` >> simp[] >> irule dft_flip_upgrade >> simp[] >>
  qexists `b.bb_instructions` >> simp[] >> conj_tac
  >- (drule dft_original_block_perm >> disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  irule dft_flip_provenance >> simp[]
QED

Theorem dft_flip_pure_tests:
  is_flippable i.inst_opcode ==>
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  (flip_operands i).inst_opcode <> INVOKE /\
  (flip_operands i).inst_opcode <> GAS /\
  ~is_terminator (flip_operands i).inst_opcode
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def, is_terminator_def] >>
  Cases_on `i.inst_operands` >> simp[flip_operands_def, is_terminator_def] >>
  Cases_on `t` >> simp[flip_operands_def, is_terminator_def] >>
  Cases_on `t'` >> simp[flip_operands_def, is_comparator_def,
    flip_comparison_opcode_def, is_terminator_def]
QED

Theorem dft_flip_tests:
  flip_rel i j ==>
  (i.inst_opcode = INVOKE <=> j.inst_opcode = INVOKE) /\
  (i.inst_opcode = GAS <=> j.inst_opcode = GAS) /\
  (is_terminator i.inst_opcode <=> is_terminator j.inst_opcode)
Proof
  simp[flip_rel_def] >> rpt strip_tac >> simp[] >>
  metis_tac[dft_flip_pure_tests]
QED

Theorem dft_flip_get_instruction:
  LIST_REL flip_rel b.bb_instructions b'.bb_instructions ==>
  OPTREL flip_rel (get_instruction b idx) (get_instruction b' idx)
Proof
  strip_tac >>
  `LENGTH b.bb_instructions = LENGTH b'.bb_instructions` by
    metis_tac[LIST_REL_LENGTH] >>
  simp[get_instruction_def] >> Cases_on `idx < LENGTH b'.bb_instructions` >> simp[] >>
  fs[LIST_REL_EL_EQN]
QED

Theorem dft_flip_deliver:
  R f g /\ br f g b b' /\ LIST_REL (dft_rel_frame R br) stk stk' /\
  flip_rel i j ==>
  dft_rel_core R br (dft_open_deliver f k b i s stk n r)
    (dft_open_deliver g k b' j s stk' n r)
Proof
  strip_tac >> drule dft_flip_tests >> strip_tac >> Cases_on `r` >>
  simp[dft_open_deliver_def, dft_rel_core_def, dft_open_continue_def] >>
  Cases_on `is_terminator j.inst_opcode` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[]
QED

Theorem dft_flip_at:
  dft_rel_interface C C' R br /\ R f g /\ br f g b b' /\
  LIST_REL (dft_rel_frame R br) stk stk' /\
  LIST_REL flip_rel b.bb_instructions b'.bb_instructions ==>
  dft_rel_core R br
    (dft_open_next a C (DftOpen (DftAt f k b s) stk n))
    (dft_open_next a C' (DftOpen (DftAt g k b' s) stk' n))
Proof
  strip_tac >> drule dft_flip_get_instruction >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  Cases_on `get_instruction b s.vs_inst_idx` >>
  Cases_on `get_instruction b' s.vs_inst_idx` >> simp[]
  >- (irule dft_rel_at >> simp[]) >> strip_tac >>
  Cases_on `x' = x`
  >- (irule dft_rel_at >> simp[]) >>
  `is_flippable x.inst_opcode /\ x' = flip_operands x` by fs[flip_rel_def] >>
  drule dft_flip_pure_tests >> strip_tac >>
  `step_inst_base x' s = step_inst_base x s` by
    metis_tac[flip_operands_step_inst_base] >>
  simp[dft_open_next_def, flip_operands_step_inst_base] >>
  irule dft_flip_deliver >> metis_tac[]
QED

Theorem dft_flip_next:
  dft_rel_interface C C' R br /\
  (!f g b b'. R f g /\ br f g b b' ==>
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions) /\
  dft_rel_core R br q q' ==>
  dft_rel_core R br (dft_open_next a C q) (dft_open_next a C' q')
Proof
  Cases_on `q` >> Cases_on `q'` >>
  rename1 `dft_rel_core R br (DftOpen c stk n) (DftOpen c' stk' n')` >>
  Cases_on `c` >> Cases_on `c'` >>
  simp[dft_rel_core_def, dft_rel_control_def] >> rpt strip_tac >> gvs[]
  >- (irule dft_rel_enter >> simp[])
  >- (irule dft_flip_at >> simp[] >> metis_tac[]) >>
  simp[dft_open_next_def] >> irule dft_rel_return >> simp[]
QED

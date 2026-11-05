(* Shape-sensitive scheduler boundaries, including the exceptional code_end ADD. *)
Theory dftShape
Ancestors
  dftNonSsa dftStructural dftDefs unitShapeDefs venomWf venomInst
  venomEffects passSharedDefs stackPlanTypes list
Libs
  BasicProvers

Theorem flip_operands_inst_wf:
  is_flippable inst.inst_opcode /\ inst_wf inst ==>
  inst_wf (flip_operands inst)
Proof
  Cases_on `inst.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  simp[inst_wf_def, flip_operands_def, is_comparator_def,
       flip_comparison_opcode_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Theorem dft_block_inst_wf:
  EVERY inst_wf bb.bb_instructions ==>
  EVERY inst_wf (dft_block order bb).bb_instructions
Proof
  strip_tac >> irule dft_block_pred >> simp[] >>
  rpt gen_tac >> strip_tac >> irule flip_operands_inst_wf >>
  gvs[EVERY_MEM]
QED

Theorem flip_operands_inst_shape:
  is_flippable inst.inst_opcode /\ inst_shape_ok inst /\
  (inst.inst_opcode <> ADD \/
   EVERY (\op. ~is_label_operand op) inst.inst_operands) ==>
  inst_shape_ok (flip_operands inst)
Proof
  Cases_on `inst.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  Cases_on `inst.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def] >>
  simp[is_comparator_def, flip_comparison_opcode_def] >>
  simp[inst_shape_ok_def, is_read0_opcode_def] >>
  simp[label_positions_ok_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[is_label_operand_def]
QED

Theorem flippable_shape_label_cases:
  is_flippable inst.inst_opcode /\ inst_shape_ok inst ==>
  EVERY (\op. ~is_label_operand op) inst.inst_operands \/
  (inst.inst_opcode = ADD /\
   ?op. inst.inst_operands = [op; Label "code_end"])
Proof
  Cases_on `inst.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  simp[inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `h'` >> simp[is_label_operand_def]
QED

Theorem dft_block_inst_shape:
  EVERY inst_shape_ok bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  EVERY inst_shape_ok (dft_block order bb).bb_instructions
Proof
  strip_tac >> irule dft_block_pred >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `inst_shape_ok i` by gvs[EVERY_MEM] >>
  drule_all flippable_shape_label_cases >> strip_tac
  >- (irule flip_operands_inst_shape >> simp[]) >>
  drule_all (INST_TYPE [alpha |-> ``:instruction``] add_label_children_sorted) >>
  disch_then (qspecl_then [`order`, `build_offspring_map bb.bb_instructions order`] mp_tac) >>
  simp[]
QED

Theorem dft_block_instruction_source:
  MEM i (dft_block order bb).bb_instructions ==>
  ?j. MEM j bb.bb_instructions /\
      (i = j \/ (i = flip_operands j /\ is_flippable j.inst_opcode))
Proof
  strip_tac >> Cases_on `is_pseudo i.inst_opcode`
  >- (`MEM i (FILTER (\i. is_pseudo i.inst_opcode)
         (dft_block order bb).bb_instructions)` by simp[MEM_FILTER] >>
      qpat_x_assum `MEM _ (FILTER _ _)` mp_tac >>
      pure_rewrite_tac[dft_block_phis] >> simp[MEM_FILTER] >>
      strip_tac >> qexists_tac `i` >> simp[]) >>
  `from_block bb.bb_instructions i` by
    (irule dft_block_from_orig >> simp[MEM_FILTER] >> metis_tac[]) >>
  gvs[from_block_def] >> metis_tac[]
QED

Theorem flip_operands_operand_mem:
  MEM op (flip_operands i).inst_operands <=> MEM op i.inst_operands
Proof
  Cases_on `i.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[] >> metis_tac[]
QED

(* These are precisely the opaque-value producers/propagators/consumers,
   along with entry parameters and entry-only termination classes. *)
Theorem flip_operands_special_opcode:
  is_flippable i.inst_opcode ==>
  ~MEM (flip_operands i).inst_opcode
    [ASSIGN; PHI; GAS; RETPC_PARAM; INVOKE; CALL; STATICCALL;
     RET; RETFMP; DRET; PARAM; FMP_PARAM; STOP; RETURN]
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  Cases_on `i.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def, is_comparator_def,
                      flip_comparison_opcode_def]
QED

Theorem dft_block_special_source:
  MEM i (dft_block order bb).bb_instructions /\
  MEM i.inst_opcode
    [ASSIGN; PHI; GAS; RETPC_PARAM; INVOKE; CALL; STATICCALL;
     RET; RETFMP; DRET; PARAM; FMP_PARAM; STOP; RETURN] ==>
  MEM i bb.bb_instructions
Proof
  strip_tac >> drule dft_block_instruction_source >> strip_tac >> gvs[] >>
  drule flip_operands_special_opcode >> simp[]
QED

Theory o1LabelFlowDftSeed
Ancestors
  o1LabelFlowLateDft dftSsaPreserve dftScheduleOrder unitShapeDefs list

(* Forward orientation: shape of the OUTPUT, rather than of the source,
   rejects a flipped code_end seed. *)
Theorem flipped_code_end_seed_invalid:
  i.inst_opcode = ADD /\ i.inst_operands = [op; Label "code_end"] /\
  label_positions_ok (flip_operands i) ==> F
Proof
  strip_tac >>
  gvs[dftDefsTheory.flip_operands_def, passSharedDefsTheory.is_comparator_def,
      label_positions_ok_def] >>
  Cases_on `op` >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem dft_block_rel_seed_retained:
  dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY label_positions_ok bb'.bb_instructions /\
  MEM i bb.bb_instructions /\ i.inst_opcode = ADD /\
  i.inst_operands = [op; Label "code_end"] ==>
  MEM i bb'.bb_instructions
Proof
  strip_tac >> drule_all dft_block_rel_member >> strip_tac >> gvs[] >>
  metis_tac[EVERY_MEM, flipped_code_end_seed_invalid]
QED

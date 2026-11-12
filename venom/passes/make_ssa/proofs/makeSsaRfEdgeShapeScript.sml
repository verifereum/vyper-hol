Theory makeSsaRfEdgeShape
Ancestors makeSsaCurrentFinalBlock
  makeSsaDefs makeSsaCurrentProps cfgTransform cfgTransformProps
          makeSsaRfWitness makeSsaRfRenameTrace venomInst list rich_list pair
  venomExecProofs
















Theorem rf_current_succ_phis_fold_lookup:
  lookup_block q bbs = SOME bb ==>
  lookup_block q (update_current_succ_phis rs p bbs succs) =
    SOME (current_block_edge_fold rs p succs bb)
Proof
  simp[current_succ_phis_fold_lookup_option]
QED











Theorem current_edge_shape_copy_shape:
  current_edge_shape old new ==>
  LIST_REL rf_copy_shape old.bb_instructions new.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN, rf_copy_shape_def] >> metis_tac[]
QED


Theorem current_edge_shape_outputs:
  current_edge_shape old new ==>
  MAP instruction_inst_outputs new.bb_instructions =
    MAP instruction_inst_outputs old.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP]
QED

Theorem rf_current_succ_phis_outputs:
  OPTION_MAP (\bb. MAP instruction_inst_outputs bb.bb_instructions)
    (lookup_block l (update_current_succ_phis rs p bbs succs)) =
  OPTION_MAP (\bb. MAP instruction_inst_outputs bb.bb_instructions) (lookup_block l bbs)
Proof
  simp[current_succ_phis_fold_lookup_option] >> Cases_on `lookup_block l bbs` >> simp[] >>
  irule current_edge_shape_outputs >> simp[current_block_edge_fold_shape]
QED






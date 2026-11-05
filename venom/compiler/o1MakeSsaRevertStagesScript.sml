Theory o1MakeSsaRevertStages
Ancestors
  o1MakeSsaCallPaths o1MakeSsaPreparation o1MakeSsaFormats o1MakeSsaCfg
  o1MakeSsaTraversalFrames unitShapeDefs makeSsaCurrentDefs list pred_set

Theorem prepared_prefix_revert_block:
  prepared_prefix a b ==> mssa_revert_block a b
Proof
  simp[prepared_prefix_def] >> strip_tac >>
  `!i. MEM i pre ==> i.inst_opcode <> INVOKE` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  simp[mssa_revert_block_def] >> strip_tac >>
  `LAST (pre ++ a.bb_instructions) = LAST a.bb_instructions` by
    (Cases_on `a.bb_instructions` >> fs[LAST_APPEND_CONS]) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

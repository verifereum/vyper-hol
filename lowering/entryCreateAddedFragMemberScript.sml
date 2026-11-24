Theory entryCreateAddedFragMember
Ancestors
  loweringShapeDefs exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousContext list rich_list

Theorem entry_shape_added_frag_member:
  entry_shape a b /\ MEM i (added_insts a b) ==> MEM i (frag_code a b)
Proof
  rw[entry_shape_def]
  >- (`frag_code a b = tail` by metis_tac[frag_code_open] >>
      `state_insts b = state_insts a ++ tail` by
        simp[state_insts_def, all_blocks_def, APPEND_ASSOC] >>
      fs[added_insts_def, DROP_LENGTH_APPEND]) >>
  `frag_code a b = tail ++ FLAT (MAP (\bb. bb.bb_instructions) front) ++
    b.cs_current_insts` by metis_tac[frag_code_closed] >>
  `state_insts b = state_insts a ++ tail ++
    FLAT (MAP (\bb. bb.bb_instructions) (REVERSE front)) ++
    b.cs_current_insts` by
    simp[state_insts_def, all_blocks_def, REVERSE_APPEND, APPEND_ASSOC] >>
  qpat_x_assum `MEM i (added_insts a b)` mp_tac >>
  pure_rewrite_tac[added_insts_def] >>
  qpat_x_assum `state_insts b = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

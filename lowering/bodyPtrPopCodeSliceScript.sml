Theory bodyPtrPopCodeSlice
Ancestors
  fragExec rich_list list

Theorem pop_fn_has_code_current_slice:
  fn_has_code sa sb fn /\ sb.cs_current_insts = pre ++ code ++ post ==>
  ?bb tail. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++ code ++ post ++ tail
Proof
  simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[APPEND_ASSOC] >> metis_tac[]
QED

Theorem pop_fn_has_code_completed_slice:
  fn_has_code sa sb fn /\ MEM bb (emitted_blocks sa sb) /\
  bb.bb_instructions = pre ++ code ++ post ==>
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ code ++ post
Proof
  simp[fn_has_code_def] >> metis_tac[]
QED

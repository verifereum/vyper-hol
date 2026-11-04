Theory algebraicOptRangeProofs
Ancestors
  rangeAnalysisDefs

(* Coincident JNZ targets select the true-edge refinement.  This is a
   computation boundary only, not a reachable-state soundness assertion. *)
Theorem ao_range_coincident_targets:
  lookup_block pred bbs = SOME bb /\
  ~NULL bb.bb_instructions /\
  LAST bb.bb_instructions = term /\
  term.inst_opcode = JNZ /\
  term.inst_operands = [cond; Label dst; Label dst] ==>
  range_branch_refine dfg bbs pred dst rs =
    range_apply_condition dfg ASSIGN_CHAIN_FUEL cond T rs
Proof
  strip_tac >> simp[range_branch_refine_def]
QED

Theorem ao_range_coincident_edge:
  lookup_block pred bbs = SOME bb /\
  ~NULL bb.bb_instructions /\
  LAST bb.bb_instructions = term /\
  term.inst_opcode = JNZ /\
  term.inst_operands = [cond; Label dst; Label dst] ==>
  range_edge_transfer_opt (dfg,bbs) pred dst (SOME rs) =
    SOME (range_apply_condition dfg ASSIGN_CHAIN_FUEL cond T rs)
Proof
  strip_tac >> simp[range_edge_transfer_opt_def] >>
  drule_all ao_range_coincident_targets >> simp[]
QED

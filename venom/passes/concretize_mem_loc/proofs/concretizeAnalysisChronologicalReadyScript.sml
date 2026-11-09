Theory concretizeAnalysisChronologicalReady
Ancestors
  concretizeAnalysisReverseTransfer frameOriginHistoryCompletedWrites
  frameOriginHistory contextCodegenRel venomExecSemantics venomWf list

Theorem origin_phi_prefix_member:
  !is i. MEM i (origin_phi_prefix is) ==>
    MEM i is /\ i.inst_opcode = PHI
Proof
  Induct >> simp[origin_phi_prefix_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> metis_tac[]
QED

(* The source belongs to the OLD log, before the simultaneous PHI batch.
   Allocation-exclusivity is deliberately not a premise of chronology. *)
Theorem joint_origin_history_phi_prefix_completed_write:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
  ~post.vs_halted /\ enters_block fn post t /\
  MEM target fn.fn_blocks /\ target.bb_label = t.vs_current_bb /\
  MEM phi (origin_phi_prefix target.bb_instructions) /\
  resolve_phi s.vs_current_bb phi.inst_operands = SOME (Var v) ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule origin_phi_prefix_member >> strip_tac >>
  drule joint_origin_history_selected_phi_completed_write >> simp[] >>
  disch_then irule >> metis_tac[]
QED

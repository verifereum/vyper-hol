Theory o1LowerDloadNonCallContinuation
Ancestors
  o1LowerDloadSegmentContinuation o1LowerDloadSuppliedSegmentNext
  o1LowerDloadUnchangedFetch o1LowerDloadOrdinaryDispatch
  o1LowerDloadFreshNext o1LowerDloadRepeatedNext
  o1LowerDloadJointRelation o1LowerDloadReadiness o1LowerDloadOccurrence
  o1PassContract ptrDiscipline venomExecSemantics venomInstProps venomWf
  contextCodegenRel venomInst venomExecProps irSupply list finite_map

Theorem ld_joint_singleton_continue[local]:
  !bb.
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 tnext fn' bb' B1 sites1 X1.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!m. exec_block m C' bb' t = exec_block m C' bb' tnext) /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) tnext
      n a U B1 HP (occurrence_step a HP H inst s1) sites1 X1 ts
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_noncall_continue:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 tnext fn' bb' B1 sites1 X1.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!m. exec_block m C' bb' t = exec_block m C' bb' tnext) /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) tnext
      n a U B1 HP (occurrence_step a HP H inst s1) sites1 X1 ts
Proof
  (* P4a in progress *) cheat
QED


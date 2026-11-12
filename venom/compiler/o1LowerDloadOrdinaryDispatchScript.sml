Theory o1LowerDloadOrdinaryDispatch
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointArithmetic o1LowerDloadJointScalar
  o1LowerDloadJointTernary o1LowerDloadJointCompare o1LowerDloadJointShift
  o1LowerDloadJointResidualScalar o1LowerDloadJointRead0 o1LowerDloadJointRead1
  o1LowerDloadJointParam o1LowerDloadJointRetpc o1LowerDloadJointAssign
  o1LowerDloadJointBump o1LowerDloadJointIdentity o1LowerDloadJointMemoryRead
  o1LowerDloadJointMemoryWrite o1LowerDloadJointCleanWrite
  o1LowerDloadJointRangeCopy o1LowerDloadJointRangeRead
  o1LowerDloadJointStorageRead o1LowerDloadJointStorageWrite
  o1LowerDloadJointInternalEffects o1LowerDloadJointExternal
  o1LowerDloadReadiness venomInstProps o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1PassContract contextCodegenRel venomInst
  venomWf ptrDiscipline venomExecSemantics list

Theorem ld_joint_ordinary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DLOAD; DLOADBYTES; ALLOCA] /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 t1 u fn'.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

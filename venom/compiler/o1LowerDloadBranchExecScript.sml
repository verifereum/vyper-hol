(* Actual branch execution transport, separate from PHI entry preservation. *)
Theory o1LowerDloadBranchExec
Ancestors
  o1LowerDloadPhiEntry o1LowerDloadJointScalar o1LowerDloadJointRelation
  ptrDiscipline venomExecSemantics venomState venomInst o1PassContract
  memLocDefs unitShapeDefs pointerConfinedDefs list

Theorem ld_joint_branch_operands_clean[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[MEM, is_pointer_preserving_op_def, mem_read_ops_def,
      mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_branch_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel' C' inst t = OK t1 /\
       s1.vs_current_bb = t1.vs_current_bb /\
       s1.vs_prev_bb = t1.vs_prev_bb /\
       s1.vs_halted = s.vs_halted /\ t1.vs_halted = t.vs_halted
Proof
  (* P4a in progress *) cheat
QED

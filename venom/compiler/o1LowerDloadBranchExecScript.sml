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
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[ld_joint_branch_operands_clean] >>
  `ld_joint_local_fields s t /\ s.vs_current_bb = t.vs_current_bb` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_control_def] >>
  qpat_x_assum `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  fs[ld_joint_local_fields_def, MEM] >>
  (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[AllCaseEqs()] >> strip_tac >>
   gvs[] >>
   `!op. MEM op inst.inst_operands ==> eval_operand op t = eval_operand op s` by
     (rpt strip_tac >> gvs[MEM] >> metis_tac[]) >>
   asm_simp_tac (srw_ss()) [] >>
   simp[jump_to_def])
QED

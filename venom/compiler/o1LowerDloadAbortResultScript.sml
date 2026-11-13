(* Terminal abort observations do not compare payload states. *)
Theory o1LowerDloadAbortResult
Ancestors
  o1LowerDloadForwardAbort o1LowerDloadJointScalar o1LowerDloadJointRelation
  ptrDiscipline o1PassContract venomExecSemantics venomState venomInst
  list option

Theorem ld_joint_forward_abort_result:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?fn' bb' t1. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = Abort reason t1 /\
    dead_result_rel D (Abort reason s1) (Abort reason t1)
Proof
  strip_tac >> drule_all ld_joint_forward_abort >>
  simp[dead_result_rel_def]
QED

Theorem ld_joint_revert_result:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ active_inst fn inst s /\
  inst.inst_opcode = REVERT /\ step_inst fuel C inst s = Abort reason s1 ==>
  ?t1. step_inst fuel C' inst t = Abort reason t1 /\
    dead_result_rel D (Abort reason s1) (Abort reason t1)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    (rpt strip_tac >> irule ld_joint_operand_defined >>
     metis_tac[ld_active_operand_ir_var]) >>
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[dead_result_rel_def] >>
  `IS_SOME (eval_operand off_op t) /\ IS_SOME (eval_operand sz_op t)` by
    metis_tac[MEM, IS_SOME_DEF] >>
  Cases_on `eval_operand off_op t` >> Cases_on `eval_operand sz_op t` >> gvs[] >>
  metis_tac[]
QED

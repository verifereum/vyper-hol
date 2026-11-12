(* Exceptional branches depend on guards and availability, not payload memory. *)
Theory o1LowerDloadExceptional
Ancestors
  o1LowerDloadJointRangeCopy o1LowerDloadJointExternal
  o1LowerDloadJointInternalEffects
  o1LowerDloadJointScalar o1LowerDloadJointRelation
  venomExecSemantics venomExecProps venomInst memLocDefs
  ptrDiscipline o1PassContract o1LowerDloadOpaque unitShapeDefs list finite_map

Theorem ld_joint_copy_abort:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\
  step_inst fuel C inst s = Abort reason s1 ==>
  ?t1. step_inst fuel C' inst t = Abort reason t1
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_create_size:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;off;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;off;sz;salt])) ==>
  eval_operand sz s = eval_operand sz t
Proof
  strip_tac >> (
  `op_prov H sz = NONE /\ op_taint tn sz = {}` by
    (drule ld_joint_external_scalar_clean >> disch_then irule >>
     gvs[MEM, mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[FILTER, SF boolSimps.COND_elim_ss]) >>
  irule ld_joint_operand_clean >>
  `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
  metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM])
QED

Theorem ld_joint_create_abort:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst fuel C inst s = Abort reason s1 ==>
  ?t1. step_inst fuel C' inst t = Abort reason t1
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_ordinary_abort:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [RETURNDATACOPY;CREATE;CREATE2] /\
  step_inst fuel C inst s = Abort reason s1 ==>
  ?t1. step_inst fuel C' inst t = Abort reason t1
Proof
  strip_tac >> Cases_on `inst.inst_opcode = RETURNDATACOPY`
  >- (drule ld_joint_copy_abort >> disch_then irule >> simp[]) >>
  drule ld_joint_create_abort >> disch_then irule >> gvs[MEM]
QED

Theorem ld_joint_static_abort:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG; SELFDESTRUCT; CALL] /\
  step_inst fuel C inst s = Abort reason s1 ==>
  ?t1. step_inst fuel C' inst t = Abort reason t1
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
      (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    (rpt strip_tac >> drule ld_joint_operand_defined >> disch_then irule >>
     metis_tac[ld_active_operand_ir_var]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[ld_eval_operands_defined, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = CALL`
  >- suspend "call" >>
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  gvs[MEM] >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[exec_write2_def, AllCaseEqs()] >> metis_tac[]
QED

Resume ld_joint_static_abort[call]:
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_ext_call_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `op_prov H val_op = NONE /\ op_taint tn val_op = {}` by
    (drule ld_joint_external_scalar_clean >> disch_then irule >>
     simp[Excl "FILTER"] >>
     gvs[Excl "FILTER", mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[FILTER, SF boolSimps.COND_elim_ss]) >>
  `eval_operand val_op s = eval_operand val_op t` by
    (irule ld_joint_operand_clean >>
     `!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  gvs[] >>
  fs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED
Finalise ld_joint_static_abort

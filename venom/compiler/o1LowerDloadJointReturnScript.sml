(* RET transports returned values, not the opaque final return token. *)
Theory o1LowerDloadJointReturn
Ancestors
  o1LowerDloadJointScalar o1LowerDloadOpaque o1LowerDloadGhost
  o1LowerDloadJointRelation o1LowerDloadEnvironment o1LowerDloadJointAssign
  o1LowerDloadOccurrence ptrDiscipline o1PassContract contextCodegenRel
  memLocDefs pointerConfinedDefs venomExecSemantics venomExecProps
  venomInst venomState list rich_list

Theorem ld_joint_ret_front:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = RET /\
  inst.inst_operands <> [] ==>
  !op. MEM op (FRONT inst.inst_operands) ==>
    eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_prov H op = NONE` by
    (drule ld_joint_scalar_no_provenance >>
     simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  rpt strip_tac >>
  `MEM op inst.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
  `op_prov H op = NONE /\ op_taint tn op = {}` by
    metis_tac[ret_operand_untainted] >>
  irule ld_joint_operand_clean >>
  metis_tac[ld_active_operand_ir_var, ret_front_non_retpc]
QED

Theorem ld_joint_ret_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = RET /\
  step_inst fuel C inst s = IntRet ir s1 ==>
  ?jr. step_inst fuel C' inst t = IntRet jr t /\
    jr.iret_values = ir.iret_values /\ ir.iret_adopt_fmp = NONE /\
    jr.iret_adopt_fmp = NONE /\ s1 = s
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
      (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    (rpt strip_tac >> drule ld_joint_operand_defined >> disch_then irule >>
     metis_tac[ld_active_operand_ir_var]) >>
  `step_inst_base inst s = IntRet ir s1` by
    gvs[step_inst_non_invoke] >>
  `inst.inst_operands <> []` by
    (strip_tac >>
     qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[eval_operands_def]) >>
  `!op. MEM op (FRONT inst.inst_operands) ==>
       eval_operand op s = eval_operand op t` by
    (drule ld_joint_ret_front >> simp[]) >>
  drule_all ret_front_transfer >> strip_tac >>
  qexists_tac `jr` >> simp[step_inst_non_invoke]
QED

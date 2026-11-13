Theory lowerDloadReachableJump
Ancestors
  lowerDloadProvenanceSupport lowerDloadJumpProducer lowerDloadSourceInterface
  lowerDloadCoverageInvariant lowerDloadReachableDiscipline
  ptrDiscipline pointerConfinedDefs contextCodegenRel memLocDefs venomInst
  o1PassContract list pred_set

Theorem ld_annotated_jump_prov:
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [JMP; JNZ; DJMP] ==>
  !op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!v. MEM (Var v) i.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `!v. op = Var v ==> v NOTIN fn_pv P fn` by metis_tac[] >>
  drule_all ld_annotated_scalar_prov >> simp[]
QED

Theorem ld_reachable_jump_backward:
  ptr_discipline lo CS vs0 /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  opaque_use_ok fn /\ MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  ld_frame_data V {v | MEM v (fn_ir_vars fn) /\ ~retpc_var fn v}
    E L H AP BP AG BH tn un s t /\
  step_inst fuelT CT i t = OK t' ==>
  ?lbl. t' = jump_to lbl t /\
    step_inst fuelS CS i s = OK (jump_to lbl s)
Proof
  strip_tac >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule ld_taint_operand_clean >>
     qexistsl_tac [`fn`, `i`, `s`] >> simp[] >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> gvs[]) >>
  `!v. MEM (Var v) i.inst_operands ==>
       v IN {v | MEM v (fn_ir_vars fn) /\ ~retpc_var fn v}` by
    (rpt strip_tac >> irule ld_original_nonopaque_operand_support >>
     simp[] >> qexists_tac `i` >> simp[] >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> gvs[]) >>
  `?P. !f. MEM f CS.ctx_functions ==> fn_ptr_ok P f` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE` by
    (rpt strip_tac >> drule_all ld_annotated_jump_prov >> simp[]) >>
  `!op. MEM op i.inst_operands ==>
       ld_op_prov AG op = NONE /\ op_taint tn op = {}` by simp[] >>
  drule ld_frame_data_vars >> strip_tac >>
  drule_all ld_jump_backward >> simp[]
QED

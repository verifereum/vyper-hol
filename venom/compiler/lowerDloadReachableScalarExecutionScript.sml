Theory lowerDloadReachableScalarExecution
Ancestors
  lowerDloadProvenanceSupport lowerDloadOrdinaryExecution lowerDloadOwnership
  lowerDloadOperand lowerDloadReachableDiscipline ptrDiscipline
  pointerConfinedDefs contextCodegenRel
  memLocDefs venomInst o1PassContract list pred_set

Theorem ld_annotated_pure_scalar_prov:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR] ==>
  !op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
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

Theorem ld_annotated_pure_scalar_backward:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR] /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE` by
    (rpt strip_tac >> drule_all ld_annotated_pure_scalar_prov >> simp[]) >>
  irule ld_owned_pure_scalar_backward >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> metis_tac[]
QED

Theorem ld_annotated_clean_scalar_backward:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule ld_taint_operand_clean >>
     qexistsl [`fn`, `i`, `s`] >> simp[] >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> gvs[]) >>
  `MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR]` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> gvs[]) >>
  drule_all ld_annotated_pure_scalar_backward >> simp[]
QED

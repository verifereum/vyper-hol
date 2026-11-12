Theory lowerDloadReachableScalarExecution
Ancestors
  lowerDloadProvenanceSupport lowerDloadOrdinaryExecution lowerDloadOwnership
  lowerDloadOperand lowerDloadReachableDiscipline ptrDiscipline
  pointerConfinedDefs contextCodegenRel
  memLocDefs venomInst o1PassContract list pred_set
  lowerDloadPairedBoundary venomExecSemantics venomState words finite_map

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
  Cases_on `i.inst_opcode = MUL`
  >- suspend "mul" >>
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

Resume ld_annotated_clean_scalar_backward[mul]:
  `MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR]` by simp[] >>
  `!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE` by
    (rpt strip_tac >> drule_all ld_annotated_pure_scalar_prov >> simp[]) >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule ld_owned_operand_defined >> simp[] >> metis_tac[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[exec_pure2_def, SimpLHS] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `?x1. eval_operand op1 s = SOME x1` by
    (Cases_on `eval_operand op1 s` >> gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `?x2. eval_operand op2 s = SOME x2` by
    (Cases_on `eval_operand op2 s` >> gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `ld_owned_value E NONE (ld_op_prov AH op1)
     (op_taint tn op1) (op_taint un op1) x1 v1 /\
   ld_owned_value E NONE (ld_op_prov AH op2)
     (op_taint tn op2) (op_taint un op2) x2 v2` by
    (conj_tac >> metis_tac[ld_owned_operand_value]) >>
  `ld_op_prov AH op1 = NONE /\ ld_op_prov AH op2 = NONE /\
   ld_mask_word (op_taint tn op1) (op_taint un op1) x1 v1 /\
   ld_mask_word (op_taint tn op2) (op_taint un op2) x2 v2` by
    gvs[ld_owned_value_def] >>
  simp[Once step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[exec_pure2_def] >>
  `ld_owned_value E NONE NONE (out_taint tn i s) (out_taint un i t)
     (x1 * x2) (v1 * v2)` by suspend "mask" >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def,
       ld_owned_vars_def, op_taint_def]
QED

Resume ld_annotated_clean_scalar_backward[mask]:
  simp[ld_owned_value_def, out_taint_def] >>
  `op_taint tn op1 = {} \/
    (op_taint tn op2 = {} /\ (x2 = 0w \/ x2 = 1w))` by
    (Cases_on `op_taint tn op1 = {}` >- simp[] >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >>
     strip_tac >> first_x_assum (qspec_then `op1` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `op_taint tn op2 = {} \/
    (op_taint tn op1 = {} /\ (x1 = 0w \/ x1 = 1w))` by
    (Cases_on `op_taint tn op2 = {}` >- simp[] >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >>
     strip_tac >> first_x_assum (qspec_then `op2` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  gvs[] >> imp_res_tac ld_mask_word_clean >> gvs[] >>
  simp[ld_mask_word_identity, WORD_MULT_CLAUSES]
QED

Finalise ld_annotated_clean_scalar_backward

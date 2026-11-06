Theory concretizePtrScalarCoreProducer
Ancestors concretizePtrReturnTransport concretizePtrTaggedSupport concretizePtrValueTransport
  concretizePtrPairedNextAttach concretizePtrPairedPrefixProbe
  concretizePtrStructuralDispatch concretizePtrEnvironmentReadProducer
  concretizePtrOpaqueRetpc concretizePtrSourceOwnership
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  ptrDiscipline pointerConfinedDefs unitShapeDefs venomExecSemantics
  memLocDefs venomState venomInst finite_map list pred_set

Theorem ptr_scalar_core_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
              op_taint tn op = {}) inst.inst_operands
Proof
  strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >>
     fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     fs[MEM] >> simp[taint_ok_def] >> metis_tac[]) >>
  `op_prov TG op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[]) >>
  simp[] >> Cases_on `op` >> simp[ptr_nonopaque_operand_def] >>
  strip_tac >>
  `retpc_use_ok inst s'` by metis_tac[opaque_use_ok_retpc_use] >>
  fs[retpc_use_ok_def, MEM] >> gvs[]
QED

Theorem ptr_scalar_core_execution[local]:
  MEM inst.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE] /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  inst.inst_outputs = [out] /\ step_inst fuel Ct inst t = OK t' ==>
  ?v. step_inst 0 C inst s = OK (update_var out v s) /\
      t' = update_var out v t
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >>
  PURE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  simp[Once opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >> gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ptr_mixed_scalar_core_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE /\
              op_taint tn op = {}) inst.inst_operands /\
  MEM inst.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?v. step_inst 0 C inst s = OK (update_var out v s) /\
    t' = update_var out v t /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out v s))
      (step_taint inst s (update_var out v s) tn)
      f g (update_var out v s) t'
Proof
  strip_tac >>
  `eval_operands inst.inst_operands s = eval_operands inst.inst_operands t` by
    (drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
  drule_all ptr_scalar_core_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `v` >> simp[] >> gvs[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def, EVERY_MEM] >>
  gvs[FLOOKUP_UPDATE]
QED

Theory runtimeSymSrcArraySubscript
Ancestors
  runtimeSymSrcEmission exprLowering compileEnv emitHelper loweringShapeDefs
  venomInst list stackPlanTypes

Theorem runtime_sym_array_subscript_loader:
  (!p t v t'. EVERY runtime_sym_inst (state_insts t) /\
    ~is_label_operand p /\ loader p t = (v,t') ==>
    EVERY runtime_sym_inst (state_insts t') /\ ~is_label_operand v) ==>
  !bop idx dyn count ws sz signed s out s'.
    EVERY runtime_sym_inst (state_insts s) /\ ~is_label_operand bop /\
    ~is_label_operand idx /\
    compile_array_subscript bop idx dyn count ws sz signed loader s = (out,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand len_op` by
    (Cases_on `dyn` >> gvs[comp_return_def, is_label_operand_def] >>
     metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts cs'') /\ ~is_label_operand is_neg` by
    (Cases_on `signed` >> gvs[comp_return_def, is_label_operand_def] >>
     qpat_assum `emit_op SLT _ _ = _`
       (mp_then Any mp_tac runtime_sym_emit_op) >>
     simp[is_label_operand_def]) >>
  qpat_assum `emit_op LT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ISZERO [is_oob] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op OR _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ISZERO [invalid] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_void ASSERT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[] >> strip_tac >>
  rename1 `emit_op MUL [idx; Lit (n2w sz)] data_state = _` >>
  `EVERY runtime_sym_inst (state_insts data_state) /\ ~is_label_operand data_ptr` by
    (Cases_on `dyn` >> gvs[comp_return_def] >>
     qpat_assum `emit_op ADD [bop; _] _ = _`
       (mp_then Any mp_tac runtime_sym_emit_op) >>
     simp[is_label_operand_def]) >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = (out,s')`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theory lowerDloadPtrReturn
Ancestors lowerDloadPtrCall lowerDloadPtrInvoke lowerDloadPtrAggregate lowerDloadPtrRel
  lowerDloadPtrPhi ptrDiscipline venomExecSemantics venomState venomInst
  memLocDefs pointerConfinedDefs finite_map list rich_list pred_set

Theorem dload_ret_operand_clean:
  i.inst_opcode = RET /\ ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  taint_ok fn tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem eval_operands_front_backwards:
  !ops ys.
    ops <> [] /\ eval_operands ops t = SOME ys /\
    (!op. MEM op (FRONT ops) ==> eval_operand op s = eval_operand op t) /\
    (!op. MEM op ops ==> (eval_operand op s = NONE <=> eval_operand op t = NONE)) ==>
    ?xs. eval_operands ops s = SOME xs /\ xs <> [] /\ FRONT xs = FRONT ys
Proof
  Induct_on `ops` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ops`
  >- (gvs[eval_operands_def, AllCaseEqs()] >>
      Cases_on `eval_operand h s` >> gvs[] >>
      qexists_tac `[x]` >> simp[]) >>
  gvs[eval_operands_def, AllCaseEqs(), FRONT_DEF]
QED

Theorem dload_ret_backwards:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = RET /\ ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  taint_ok fn tn i s /\
  (!a. MEM (Var a) (FRONT i.inst_operands) ==> a IN V) /\
  (!a. MEM (Var a) i.inst_operands ==>
    (lookup_var a s = NONE <=> lookup_var a t = NONE)) /\
  step_inst fuel Ct i t = IntRet rt t_end ==>
  ?rs s_end. step_inst fuel Cs i s = IntRet rs s_end /\
    rs.iret_values = rt.iret_values /\ rs.iret_adopt_fmp = NONE /\
    rt.iret_adopt_fmp = NONE /\ s_end = s /\ t_end = t
Proof
  rpt strip_tac >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t.vs_labels` by
    metis_tac[dload_boundary_environment, dload_equal_environment_code] >>
  `!op. MEM op i.inst_operands ==>
     (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> metis_tac[]) >>
  `i.inst_operands <> []` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operands_def]) >>
  `!op. MEM op (FRONT i.inst_operands) ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `MEM op i.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
     drule_all dload_ret_operand_clean >> strip_tac >>
     irule scalar_operand_equal >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all eval_operands_front_backwards >> strip_tac >>
  qexists_tac `<|iret_values := FRONT xs; iret_adopt_fmp := NONE|>` >>
  Cases_on `xs` >> gvs[]
QED

Theory lowerDloadPtrInvoke
Ancestors lowerDloadPtrCall lowerDloadPtrRel ptrDiscipline
  venomExecSemantics venomState venomInst list rich_list pred_set

Theorem dload_param_values_cons:
  LENGTH PG = LENGTH xs /\ LENGTH PH = LENGTH ys /\
  dload_value_word fs {} p q x y /\ dload_param_values fs PG PH xs ys ==>
  dload_param_values fs (p::PG) (q::PH) (x::xs) (y::ys)
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN] >> strip_tac >>
  gen_tac >> Cases_on `n` >> simp[EL_GENLIST] >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[EL_GENLIST]
QED

Theorem dload_matched_operands_backwards:
  !ops ys.
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) ops ==> v IN V) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  eval_operands ops t = SOME ys ==>
  ?xs. eval_operands ops s = SOME xs /\
    LENGTH xs = LENGTH ops /\ LENGTH ys = LENGTH ops /\
    dload_param_values fs (MAP (op_prov G) ops) (MAP (op_prov H) ops) xs ys
Proof
  Induct_on `ops`
  >- simp[eval_operands_def, dload_param_values_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  rename1 `eval_operand h t = SOME y` >>
  `!v. h = Var v ==> v IN V` by metis_tac[] >>
  drule_all dload_matched_operand_defined >> strip_tac >>
  Cases_on `eval_operand h s` >- gvs[] >>
  rename1 `eval_operand h s = SOME x` >>
  `dload_value_word fs {} (op_prov G h) (op_prov H h) x y` by
    (drule_all dload_matched_operand >> simp[]) >>
  qexists_tac `x::xs` >>
  simp[eval_operands_def] >>
  irule dload_param_values_cons >> simp[]
QED

Theorem dload_invoke_setup_backwards:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  decode_invoke i = SOME (name,ops) /\ i.inst_opcode = INVOKE /\
  taint_ok caller tn i s /\ (!v. MEM (Var v) ops ==> v IN V) /\
  eval_operands ops t = SOME ys /\ ~NULL fn.fn_blocks /\
  setup_callee gn ys t = SOME ct ==>
  ?xs cs. eval_operands ops s = SOME xs /\
    setup_callee fn xs s = SOME cs /\
    dload_param_values fs (MAP (op_prov G) ops) (MAP (op_prov H) ops)
      cs.vs_params ct.vs_params
Proof
  rpt strip_tac >>
  `!op. MEM op ops ==> MEM op i.inst_operands` by
    (gvs[decode_invoke_def, AllCaseEqs()] >> simp[]) >>
  `!op. MEM op ops ==> op_taint tn op = {}` by
    metis_tac[dload_invoke_operand_untainted] >>
  drule_all dload_matched_operands_backwards >> strip_tac >>
  `?cs. setup_callee fn xs s = SOME cs` by simp[setup_callee_def] >>
  qexistsl_tac [`xs`, `cs`] >> simp[] >>
  drule_all dload_setup_parameters >> simp[]
QED

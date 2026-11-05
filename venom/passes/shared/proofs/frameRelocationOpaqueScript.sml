Theory frameRelocationOpaque
Ancestors frameRelocationValues o1PassContract unitShapeDefs ptrDiscipline
  venomExecSemantics venomState venomInst list rich_list finite_map

Theorem o1_retpc_operand_use:
  o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  retpc_var fn v /\ MEM (Var v) inst.inst_operands ==>
  retpc_use_ok inst v
Proof
  metis_tac[o1_fn_shape_def, fn_shape_ok_def, opaque_use_ok_retpc_use]
QED

Theorem disciplined_retpc_operand_use:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  retpc_var fn v /\ MEM (Var v) inst.inst_operands ==>
  inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
  (inst.inst_opcode = RET /\
   ?front. inst.inst_operands = front ++ [Var v] /\ ~MEM (Var v) front)
Proof
  strip_tac >> drule_all o1_retpc_operand_use >>
  gvs[retpc_use_ok_def, fn_ptr_ok_def] >> metis_tac[]
QED

Theorem retpc_excluded_from_return_front:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = RET /\
  retpc_var fn v ==>
  ~MEM (Var v) (FRONT inst.inst_operands)
Proof
  rpt strip_tac >>
  `MEM (Var v) inst.inst_operands` by
    (Cases_on `inst.inst_operands = []` >> gvs[] >>
     metis_tac[APPEND_FRONT_LAST, MEM_APPEND]) >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def] >>
  rpt strip_tac >> gvs[FRONT_APPEND]
QED

Theorem opaque_return_token_step:
  inst.inst_opcode = RET /\ eval_operands inst.inst_operands s = SOME (vals ++ [pc]) ==>
  step_inst_base inst s = IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s
Proof
  Cases_on `vals` >> simp[step_inst_base_def, FRONT_DEF, FRONT_APPEND]
QED

Theorem setup_callee_opaque_token:
  ~NULL fn.fn_blocks ==>
  ?s'. setup_callee fn args s = SOME s' /\
    s'.vs_vars = FEMPTY /\ s'.vs_params = args /\
    s'.vs_return_pc_token = (if NULL args then 0w else LAST args)
Proof
  simp[setup_callee_def]
QED

Theorem o1_retpc_output_source:
  o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  MEM v inst.inst_outputs /\ retpc_var fn v ==>
  inst.inst_opcode = RETPC_PARAM \/
  (inst.inst_opcode = ASSIGN /\ ?w. inst.inst_operands = [Var w] /\ retpc_var fn w) \/
  (inst.inst_opcode = PHI /\
   (?w. MEM (Var w) inst.inst_operands /\ retpc_var fn w) /\
   (!w. MEM (Var w) inst.inst_operands ==> retpc_var fn w))
Proof
  simp[o1_fn_shape_def, fn_shape_ok_def, unitShapeDefsTheory.retpc_shape_ok_def] >>
  rpt strip_tac >>
  qpat_x_assum `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs /\ retpc_var fn x ==> _`
    drule_all >> simp[]
QED

Theorem opaque_assign_definedness:
  variable_domains s t /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    variable_domains (update_var v x s) (update_var v y t)
Proof
  strip_tac >>
  `eval_operand op t <> NONE` by metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE] >>
  Cases_on `eval_operand op t` >> gvs[] >>
  simp[step_inst_base_def, variable_domains_update]
QED

Theorem opaque_phi_definedness:
  variable_domains s t /\ s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb ==>
  (eval_one_phi s inst = NONE <=> eval_one_phi t inst = NONE)
Proof
  strip_tac >> Cases_on `inst.inst_outputs` >> simp[eval_one_phi_def] >>
  rename1 `h::outs` >> Cases_on `outs` >> simp[] >>
  Cases_on `t.vs_prev_bb` >> simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  drule_all operand_domain_agreement >>
  disch_then (qspec_then `x'` mp_tac) >>
  Cases_on `eval_operand x' s` >> Cases_on `eval_operand x' t` >> simp[]
QED

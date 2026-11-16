Theory loweringBudgetCreateOracleTransport
Ancestors
  venomExecSemantics venomCallOracleDefs venomState extCallOracle list

Theorem create_step_same_outcome_head:
  !fuel ctx i s t oc os rest.
    MEM i.inst_opcode [CREATE; CREATE2] /\
    s.vs_outcomes = oc::os /\
    step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx i (s with vs_outcomes := oc::rest) =
      OK (t with vs_outcomes := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. eval_operand op (s with vs_outcomes := oc::rest) =
        eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `eval_operands i.inst_operands (s with vs_outcomes := oc::rest) =
   eval_operands i.inst_operands s` by
    (irule eval_operands_agree >> simp[]) >>
  gvs[MEM] >>
  gvs[Once step_inst_def] >>
  gvs[step_inst_base_opcode_eqs, exec_create_def, AllCaseEqs()] >>
  simp[Once step_inst_def, step_inst_base_opcode_eqs, exec_create_def] >>
  simp[venom_create_request_def, read_memory_def, take_outcome_def,
       computed_precompile_def, update_var_def]
QED

Theory loweringBudgetNonconsumingOracleTransport
Ancestors
  venomExecSemantics venomState oracleStateProps opcodeClass ptrSafeRun list

Theorem pack_dret_dynamic_outcomes_update[local]:
  !pairs cursor s ptrs fc t os.
    pack_dret_dynamic cursor pairs s = (ptrs,fc,t) ==>
    pack_dret_dynamic cursor pairs (s with vs_outcomes := os) =
      (ptrs,fc,t with vs_outcomes := os)
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def, mcopy_def, write_memory_with_expansion_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `os` mp_tac) >> simp[]
QED

(* Select one checked dispatch equation before simplifying the opcode body. *)
val outcome_opcode_eqs = map
  (fn th => (rhs (fst (dest_imp (snd (strip_forall (concl th))))), th))
  (CONJUNCTS step_inst_base_opcode_eqs);

fun outcome_opcode_tac eq =
  PURE_ONCE_REWRITE_TAC [MATCH_MP
    (#2 (valOf (List.find
      (fn (key, _) => aconv key (rhs (concl eq))) outcome_opcode_eqs))) eq];

Theorem nonconsuming_step_outcomes_update:
  !fuel ctx i s t os.
    i.inst_opcode <> INVOKE /\
    ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
    step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx i (s with vs_outcomes := os) =
      OK (t with vs_outcomes := os)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. eval_operand op (s with vs_outcomes := os) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `!ops. eval_operands ops (s with vs_outcomes := os) = eval_operands ops s` by
    (gen_tac >> irule eval_operands_agree >> simp[]) >>
  gvs[Once step_inst_def] >> simp[Once step_inst_def] >>
  Cases_on `i.inst_opcode` >> gvs[MEM] >>
  qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
  qpat_assum `i.inst_opcode = _` outcome_opcode_tac >>
  pure_rewrite_tac[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_gas_def, exec_alloca_def] >>
  simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
       istore_def, write_memory_with_expansion_def, mcopy_def,
       jump_to_def, mload_def, sload_def, tload_def,
       contract_storage_def, contract_transient_def] >>
  qpat_x_assum `_ = OK t` mp_tac >> pairarg_tac >> simp[]
QED

Theorem intret_outcomes_update:
  !fuel ctx i s ret t os.
    step_inst fuel ctx i s = IntRet ret t ==>
    step_inst fuel ctx i (s with vs_outcomes := os) =
      IntRet ret (t with vs_outcomes := os)
Proof
  rpt gen_tac >> strip_tac >>
  `i.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `!op. eval_operand op (s with vs_outcomes := os) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `!ops. eval_operands ops (s with vs_outcomes := os) = eval_operands ops s` by
    (gen_tac >> irule eval_operands_agree >> simp[]) >>
  gvs[Once step_inst_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[Once step_inst_def, step_inst_base_opcode_eqs] >>
  qpat_x_assum `_ = IntRet ret t` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule pack_dret_dynamic_outcomes_update >>
  disch_then (qspec_then `os` mp_tac) >> simp[]
QED

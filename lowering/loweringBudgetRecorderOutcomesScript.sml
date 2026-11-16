Theory loweringBudgetRecorderOutcomes
Ancestors
  loweringCallBudgetHistory oracleExecProps calleeTransport opcodeClass
  fnBlockBodySteps venomInstProofs1 venomExecProofs contextCodegenRel
  venomExecSemantics venomCallOracleDefs venomState list rich_list

Theorem budget_enters_block_outcomes[local]:
  enters_block fn s t ==> t.vs_outcomes = s.vs_outcomes
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_outcomes`) >> simp[]
QED

Theorem budget_exec_call_outcomes[local]:
  (exec_ext_call inst s gas addr value ao az ro rz static = OK t ==>
    t.vs_outcomes = DROP 1 s.vs_outcomes) /\
  (exec_delegatecall inst s gas addr ao az ro rz = OK t ==>
    t.vs_outcomes = DROP 1 s.vs_outcomes) /\
  (exec_create inst s value off sz salt = OK t ==>
    t.vs_outcomes = DROP 1 s.vs_outcomes)
Proof
  rpt conj_tac >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
    extract_venom_result_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def] >>
  Cases_on `s.vs_outcomes` >> gvs[extCallOracleTheory.take_outcome_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem budget_step_outcomes[local]:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  t.vs_outcomes =
    DROP (if MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
          then 1 else 0) s.vs_outcomes
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[] >> gvs[Once step_inst_def] >>
      qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      simp[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      rpt strip_tac >> metis_tac[budget_exec_call_outcomes]) >>
  gvs[] >> metis_tac[step_inst_noninvoke_oracle]
QED

Theorem budget_pack_dret_outcomes[local]:
  !pairs cursor s ptrs fc t.
    pack_dret_dynamic cursor pairs s = (ptrs,fc,t) ==>
    t.vs_outcomes = s.vs_outcomes
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem budget_intret_outcomes[local]:
  step_inst fuel ctx inst s = IntRet ret t ==> t.vs_outcomes = s.vs_outcomes
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[ptrSafeRunTheory.step_inst_intret_not_invoke] >>
  gvs[Once step_inst_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), write_memory_with_expansion_def] >>
  pairarg_tac >> gvs[] >>
  drule budget_pack_dret_outcomes >> simp[]
QED

Theorem budget_path_outcomes[local]:
  !checked cfg p h marks q.
    lower_budget_path checked cfg p h marks q ==>
    q.bp_state.vs_outcomes = DROP (lower_history_count h) p.bp_state.vs_outcomes
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[lower_history_count_def, FILTER_APPEND, lower_event_consumes_def]
  >- (drule_all budget_step_outcomes >>
      Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` >>
      fs[MEM] >> strip_tac >>
      pure_rewrite_tac[DROP_DROP_T] >>
      AP_THM_TAC >> AP_TERM_TAC >> decide_tac)
  >- (drule budget_enters_block_outcomes >> strip_tac >>
      `i.inst_opcode <> INVOKE /\
       ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by
        (Cases_on `i.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
      drule_all budget_step_outcomes >> gvs[])
  >- (imp_res_tac setup_callee_oracle >>
      imp_res_tac budget_enters_block_outcomes >> gvs[])
  >> imp_res_tac budget_intret_outcomes >>
  imp_res_tac bind_outputs_oracle >> gvs[]
QED

Theorem lower_budget_path_outcomes:
  !checked D lo explicit ctx p h marks q.
    lower_budget_path checked (D,lo,explicit,ctx) p h marks q ==>
    q.bp_state.vs_outcomes = DROP (lower_history_count h) p.bp_state.vs_outcomes
Proof
  metis_tac[budget_path_outcomes]
QED

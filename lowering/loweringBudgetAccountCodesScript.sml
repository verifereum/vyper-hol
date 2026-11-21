(* Account code length on the unchecked recorder path. *)
Theory loweringBudgetAccountCodes
Ancestors
  loweringCallBudgetHistory loweringBudgetRecorderOutcomes contextCodegenRel
  e2eDefs vyperLoweringCorrect vyperRuntimeAccounts vyperTypeInitialState
  vyperTypeInvariants exprSimHypsDefs unitTransformDefs vfmState extCallOracle
  venomCallOracleDefs venomExecSemantics venomInst venomState venomEffects
  venomInstProofs1 venomInstProofs3 venomExecProofs calleeTransport opcodeClass
  ptrSafeRun list rich_list combin arithmetic

Definition account_code_lengths_ok_def:
  account_code_lengths_ok accounts <=>
    !addr. LENGTH (lookup_account addr accounts).code <= 24576
End

Theorem initial_account_codes_after_transfer:
  machine_well_typed am ==>
  account_code_lengths_ok (accounts_after_transfer tx am.accounts)
Proof
  strip_tac >>
  `!addr. (accounts_after_transfer tx am.accounts addr).code =
          (am.accounts addr).code` by
    (gen_tac >> rw[accounts_after_transfer_def, lookup_account_def,
                   update_account_def, combinTheory.APPLY_UPDATE_THM] >>
     rpt IF_CASES_TAC >> simp[]) >>
  gvs[account_code_lengths_ok_def, lookup_account_def] >>
  drule machine_well_typed_accounts >>
  simp[accounts_well_typed_def, account_well_typed_def, lookup_account_def] >>
  metis_tac[]
QED

Theorem account_codes_enters_block:
  enters_block fn s t ==> t.vs_accounts = s.vs_accounts
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_accounts`) >> simp[]
QED

Theorem account_codes_of_runtime_accounts[local]:
  accounts_runtime_well_typed accounts ==> account_code_lengths_ok accounts
Proof
  simp[accounts_runtime_well_typed_def, account_runtime_well_typed_def,
       account_code_lengths_ok_def] >>
  metis_tac[]
QED

Theorem account_codes_take_outcome[local]:
  outcomes_accounts_typed (SOME os) /\ account_code_lengths_ok rq.cr_accounts ==>
  account_code_lengths_ok (FST (take_outcome rq os)).co_accounts
Proof
  Cases_on `os` >>
  gvs[outcomes_accounts_typed_def, take_outcome_def, failed_outcome_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  metis_tac[account_codes_of_runtime_accounts]
QED

Theorem account_codes_adopt_outcome[local]:
  account_code_lengths_ok s.vs_accounts /\
  outcomes_accounts_typed (SOME s.vs_outcomes) /\
  rq.cr_accounts = s.vs_accounts ==>
  account_code_lengths_ok
    (FST (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
       (s.vs_accounts,s.vs_transient,s.vs_logs)))
Proof
  strip_tac >>
  `account_code_lengths_ok rq.cr_accounts` by metis_tac[] >>
  drule_all account_codes_take_outcome >>
  simp[adopt_outcome_def] >> metis_tac[]
QED

Theorem account_codes_effect_step[local]:
  account_code_lengths_ok s.vs_accounts /\ outcomes_accounts_typed (SOME s.vs_outcomes) ==>
  (exec_ext_call inst s gas addr value ao az ro rz static = OK t ==>
     account_code_lengths_ok t.vs_accounts) /\
  (exec_delegatecall inst s gas addr ao az ro rz = OK t ==>
     account_code_lengths_ok t.vs_accounts) /\
  (exec_create inst s value off sz salt = OK t ==>
     account_code_lengths_ok t.vs_accounts)
Proof
  strip_tac >> rpt conj_tac >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[update_var_def] >>
  irule account_codes_adopt_outcome >>
  simp[venom_call_request_def, venom_create_request_def]
QED

Theorem account_codes_sstore[local]:
  account_code_lengths_ok s.vs_accounts ==>
  account_code_lengths_ok (sstore key value s).vs_accounts
Proof
  simp[sstore_def, account_code_lengths_ok_def, lookup_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  strip_tac >> gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem account_codes_base_step[local]:
  account_code_lengths_ok s.vs_accounts /\ outcomes_accounts_typed (SOME s.vs_outcomes) /\
  step_inst_base i s = OK t ==>
  account_code_lengths_ok t.vs_accounts
Proof
  strip_tac >>
  Cases_on `is_terminator i.inst_opcode`
  >- (drule_all step_inst_base_ok_terminator_jump >> strip_tac >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def]) >>
  Cases_on `i.inst_opcode = INVOKE` >> fs[step_inst_base_opcode_eqs] >>
  Cases_on `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                               ALLOCA;SSTORE]`
  >- (fs[MEM] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_alloca_def, exec_write2_def,
          update_var_def] >>
      metis_tac[account_codes_effect_step, account_codes_sstore]) >>
  `~is_alloca_op i.inst_opcode /\
   Eff_BALANCE NOTIN write_effects i.inst_opcode /\
   Eff_STORAGE NOTIN write_effects i.inst_opcode` by
    (Cases_on `i.inst_opcode` >>
     gvs[is_terminator_def, is_alloca_op_def, write_effects_def, empty_effects_def]) >>
  metis_tac[step_inst_base_preserves_accounts]
QED

Theorem account_codes_pack_dret[local]:
  !pairs cursor s ptrs fc t.
    pack_dret_dynamic cursor pairs s = (ptrs,fc,t) ==>
    t.vs_accounts = s.vs_accounts
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem account_codes_intret[local]:
  step_inst fuel ctx inst s = IntRet ret t ==> t.vs_accounts = s.vs_accounts
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[ptrSafeRunTheory.step_inst_intret_not_invoke] >>
  gvs[Once step_inst_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), write_memory_with_expansion_def] >>
  pairarg_tac >> gvs[] >>
  drule account_codes_pack_dret >> simp[]
QED

Theorem account_codes_outcomes_from_root[local]:
  lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) ==>
  outcomes_accounts_typed (SOME q.bp_state.vs_outcomes)
Proof
  strip_tac >> drule lower_budget_path_outcomes >>
  fs[outcomes_accounts_typed_def, EVERY_DROP]
QED

Theorem lower_budget_path_account_code_lengths:
  lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
  account_code_lengths_ok root.bp_state.vs_accounts /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) ==>
  account_code_lengths_ok q.bp_state.vs_accounts
Proof
  qsuff_tac
    `!checked cfg root h marks q.
      lower_budget_path checked cfg root h marks q ==>
      !D lo explicit ctx. cfg = (D,lo,explicit,ctx) /\
        account_code_lengths_ok root.bp_state.vs_accounts /\
        outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) ==>
      account_code_lengths_ok q.bp_state.vs_accounts`
  >- metis_tac[] >>
  ho_match_mp_tac lower_budget_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[]
  >- metis_tac[account_codes_base_step, account_codes_outcomes_from_root,
               step_inst_non_invoke]
  >- (`i.inst_opcode <> INVOKE` by
        (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
      metis_tac[account_codes_base_step, account_codes_outcomes_from_root,
                step_inst_non_invoke, account_codes_enters_block])
  >- (imp_res_tac account_codes_enters_block >> gvs[setup_callee_def, AllCaseEqs()]) >>
  imp_res_tac account_codes_intret >>
  imp_res_tac bind_outputs_shared_fields >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def]
QED

(* A call-free constructor certificate is independent of callee outcomes. *)
Theory deployUnitOutcomesTransport
Ancestors
  deployUnitExecution deployOutcomesFreeDeploy
  loweringBudgetNonconsumingOracleTransport
  ctorDeployLoweringSource ctorDeployDefs e2eDeployDefs compileVyper
  fragGasOrigin fragGasOriginPtr ptrSafeRun venomState dftCommutation list

Theorem deploy_storage_ok_outcomes[local]:
  deploy_source_ok tops am tx /\ tx.function_name = "__init__" ==>
  !os gs. deploy_storage_ok tops am tx os gs =
    deploy_storage_ok tops am tx [] gs
Proof
  strip_tac >> simp[deploy_storage_ok_def, deploy_storage_trace_call_free]
QED

Theorem deploy_certificate_outcomes_transport:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
  deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx
    dunit vs ==>
  deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx
    dunit (vs with vs_outcomes := os)
Proof
  strip_tac >>
  drule_all deploy_entry_excludes_outcomes >> strip_tac >>
  drule_all load_contract_trace_call_free >> strip_tac >>
  drule_all deploy_storage_ok_outcomes >> strip_tac >>
  gvs[deploy_unit_execution_correct_with_def] >>
  qexists_tac `shadow_func` >>
  simp[venom_state_fupdcanon]
  >- (disj1_tac >> simp[] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`] >>
      drule_all (SRULE [] gas_origin_ptr_focus_outcomes_update) >>
      disch_then (qspec_then `os` (assume_tac o SRULE [venom_state_fupdcanon])) >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >> simp[] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`] >>
      drule_all (SRULE [] gas_origin_ptr_focus_outcomes_update) >>
      disch_then (qspec_then `os` (assume_tac o SRULE [venom_state_fupdcanon])) >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  qexists_tac `map_result_state (\t. t with vs_outcomes := os) r` >>
  simp[exit_result_outcomes_update] >> conj_tac
  >- (drule_all (SRULE [] gas_origin_path_outcomes_update) >>
      disch_then (qspec_then `os` (assume_tac o SRULE [venom_state_fupdcanon])) >>
      metis_tac[]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
  simp[] >> gen_tac >>
  qpat_x_assum `!fuel. ptr_safe_blocks _ _ _ _ _ _ _ _ _`
    (qspec_then `fuel` assume_tac) >>
  drule_all (SRULE [] (cj 3 ptr_safe_outcomes_update)) >>
  disch_then (qspecl_then [`deploy_dead H tops runtime_bc am tx`,
    `imm_len tops`, `fuel`, `dunit.cu_context`, `[]`, `FEMPTY`, `entry_taint`,
    `vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>`,
    `os`] mp_tac) >>
  simp[venom_state_fupdcanon]
QED

(* Concrete typing and entry facts for the p23 deploy-and-call witness.
   The full premise mirror and lifecycle assembly are added after their
   shared interfaces are fixed. *)
Theory e2eWitness
Ancestors
  e2eWitnessCompute e2eDefs e2eDeployDefs
  supportedProgram immutableSectionRel alist integer_word option
Libs
  computeLib wordsLib


val p23_check_dep = EVAL ``check_contract T [] 2w [(NONE, p23_tops)]``;
val p23_check_run = EVAL ``check_contract F [] 2w [(NONE, p23_tops)]``;
val p23_deploy_code_length_eval = EVAL ``LENGTH p23_deploy_bc``;
val p23_runtime_length_eval = EVAL ``LENGTH p23_runtime_bc``;
val p23_initial_imms = EVAL
  ``initial_immutables (type_env_all_modules [(NONE,p23_tops)]) [(NONE,p23_tops)]``;

val p23_constants_eval = EVAL
  ``evaluate_all_constants
      (deploy_evaluation_context p23_tops initial_machine_state p23_deploy_tx)
      (initial_machine_state with
        <| immutables := [(2w, THE (initial_immutables
             (type_env_all_modules [(NONE,p23_tops)]) [(NONE,p23_tops)]))];
           exports := [(2w,[])] |>) 2w [(NONE,p23_tops)]``;
val p23_constants_eval_expanded = SIMP_RULE (srw_ss())
  [vyperInterpreterTheory.initial_machine_state_def, p23_deploy_tx_def,
   vyperContextTheory.empty_call_txn_def, p23_initial_imms] p23_constants_eval;

Theorem p23_deploy_typing:
  deploy_typing_ok p23_tops initial_machine_state p23_deploy_tx
Proof
  simp[deploy_typing_ok_constants_ready,
       vyperInterpreterTheory.initial_machine_state_def,
       p23_deploy_tx_def, vyperContextTheory.empty_call_txn_def,
       p23_check_dep, p23_check_run, p23_initial_imms] >>
  simp[vyperTypeInitialStateTheory.machine_well_typed_def,
       vyperTypeInvariantsTheory.accounts_well_typed_def,
       vyperTypeInvariantsTheory.account_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def,
       vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
       p23_deploy_code_length_eval,
       vyperTypeEntryReadinessTheory.checked_deployment_constants_ready_def] >>
  simp[p23_constants_eval_expanded,
       vyperTypeEntryReadinessTheory.deployment_constants_output_typed_def,
       vyperTypeInvariantsTheory.imms_well_typed_def,
       p23_tops_def] >>
  rpt gen_tac >> Cases_on `id = "X"` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def,
                       vyperTypingTheory.well_formed_type_value_def]
QED

val p23_constructor_encoding_eval = EVAL
  ``constructor_args_encode p23_tops p23_deploy_tx []``;
val p23_deploy_env_eval = EVAL
  ``tx_block_fields_rel p23_deploy_tx p23_tx_params``;

(* No account holds any balance before the deployment. *)
Theorem p23_total_balance_empty[local]:
  vfmTotalBalance$total_balance empty_accounts = 0
Proof
  simp[vfmTotalBalanceTheory.total_balance_def, pred_setTheory.SUM_IMAGE_ZERO,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def]
QED

Theorem p23_deploy_state:
  deploy_state_rel p23_tops p23_deploy_bc initial_machine_state p23_deploy_tx
    p23_es_dep
Proof
  rewrite_tac[deploy_state_rel_def, p23_constructor_encoding_eval,
              p23_deploy_env_eval] >>
  qexistsl [`p23_frame p23_deploy_bc [] (Code 2w)`,
            `p23_dep_rollback`, `[]`] >>
  rewrite_tac[p23_constructor_encoding_eval, p23_deploy_env_eval] >>
  simp[p23_es_dep_def, p23_frame_def, p23_dep_rollback_def] >>
  simp[vfmExecutionPropTheory.wf_state_def,
       vfmExecutionPropTheory.wf_context_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmExecutionPropTheory.stack_room_ok_def,
       vfmExecutionPropTheory.gas_stack_ok_def,
       vfmExecutionPropTheory.outputTo_consistent_stack_def,
       vfmExecutionPropTheory.outputTo_consistent_ctx_def,
       vfmExecutionPropTheory.wf_accounts_def,
       vfmStateTheory.empty_accounts_def,
       p23_deploy_tx_def, vyperContextTheory.empty_call_txn_def,
       vyperInterpreterTheory.initial_machine_state_def,
       value_transfer_ok_def, accounts_after_transfer_def] >>
  simp[layouts_agree_def, p23_tops_def,
       vfmStateTheory.account_empty_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.empty_accounts_def, vfmStateTheory.empty_account_state_def,
       vyperInterpreterTheory.bind_arguments_def, listTheory.REV_DEF,
       tx_block_fields_rel_def, p23_tx_params_def,
       loweringStateRelDefsTheory.tx_env_ok_def,
       vfmTotalBalanceTheory.balance_bounded_def, p23_total_balance_empty,
       vfmExecutionPropTheory.all_accounts_def]
QED

val p23_call_machine_eval = EVAL ``p23_am_call``;

Theorem p23_source_typing:
  source_typing_ok p23_tops p23_am_call p23_call_tx
Proof
  simp[source_typing_ok_def, p23_call_machine_eval, p23_call_tx_def,
       vyperContextTheory.empty_call_txn_def, p23_check_run,
       account_immutables_def,
       vyperTypeInitialStateTheory.machine_well_typed_def] >>
  simp[p23_tops_def, vyperTypeContractTheory.constants_fold_module_def,
       vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
       p23_runtime_length_eval,
       p23_get_calldata_def] >>
  conj_tac >-
   (simp[vyperTypeContractSoundnessTheory.checked_contract_runtime_ready_def,
         vyperTypeContractTheory.exports_ok_def,
         vyperABIEntriesTheory.abi_deployed_signatures_def,
         vyperABIEntriesTheory.abi_external_signatures_def,
         vyperABIEntriesTheory.abi_decl_signatures_def,
         vyperTypeContractTheory.var_allocated_def,
         vyperStateTheory.find_var_decl_by_name_def] >>
    rw[vyperTypeInitialStateTheory.immutables_ready_def,
       vyperStateTheory.get_source_immutables_def,
       vyperInterpreterTheory.initial_evaluation_context_def,
       vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
    gvs[vyperStateTheory.find_var_decl_by_name_def] >> EVAL_TAC) >>
  conj_tac >- (rw[vyperTypeInvariantsTheory.accounts_well_typed_def] >>
    Cases_on `addr = 2w` >>
    simp[vyperTypeInvariantsTheory.account_well_typed_def,
         vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]) >>
  simp[vyperTypeInvariantsTheory.imms_well_typed_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt gen_tac >> Cases_on `id = "X"` >> simp[] >>
  rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def,
                       vyperTypingTheory.well_formed_type_value_def]
QED
Theorem p23_immutables_section:
  immutables_section_rel p23_tops
    (account_immutables p23_am_dep_post p23_deploy_tx.target)
    (word_to_bytes (42w : bytes32) T)
Proof
  simp[immutableSectionRelTheory.immutables_section_rel_def,
       account_immutables_def, p23_am_dep_post_def, p23_deploy_tx_def,
       vyperContextTheory.empty_call_txn_def, p23_tops_def] >>
  conj_tac >- EVAL_TAC >>
  rpt gen_tac >>
  simp[listTheory.APPEND_EQ_CONS] >>
  rpt strip_tac >> gvs[listTheory.APPEND_EQ_CONS] >>
  qexistsl [`BaseTV (UintT 256)`, `IntV 42`] >> EVAL_TAC >>
  simp[integerTheory.INT_LT_REFL] >> EVAL_TAC
QED
val p23_get_lookup_eval = EVAL
  ``vyperInterpreter$lookup_function NONE "get" External p23_tops``;

Theorem p23_valid_call:
  valid_vyper_call p23_tops p23_call_tx p23_get_calldata (BaseT (UintT 256))
Proof
  simp[valid_vyper_call_def, p23_call_tx_def,
       vyperContextTheory.empty_call_txn_def, p23_get_lookup_eval,
       vyperInterpreterTheory.bind_arguments_def,
       selectorDispatchTheory.calldata_encodes_def,
       p23_get_calldata_encodes]
QED

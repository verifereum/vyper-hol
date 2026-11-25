(* Closed deploy-and-call premise witness, with concrete typing, finite-storage,
   entry-state and result facts for the canonical p23 fixture. *)
Theory e2eWitness
Ancestors
  e2eWitnessCompute e2eDefs e2eDeployDefs
  e2eDeployed
  immutableSectionRel alist integer_word option vyperStorageFootprint
  compileVyper e2eProducers e2eCorrectness callTrace frameOutcome
  vyperCalldata vyperInterpreter
Libs
  finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

(* The shared and frame-specific premises of the deploy and call tops. *)
Definition vyper_deploy_and_call_premises_def:
  vyper_deploy_and_call_premises fin policy tops deploy_bc runtime_bc
      am_dep tx_dep es_dep am_call tx_call es_call H <=>
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok tops am_dep tx_dep /\
    deploy_state_rel tops deploy_bc am_dep tx_dep es_dep /\
    LENGTH (call_trace es_dep) < 2 ** 64 /\
    source_typing_ok tops am_call tx_call /\
    call_state_rel tops runtime_bc am_call tx_call es_call /\
    LENGTH (call_trace es_call) < 2 ** 64 /\
    storage_ok H am_call tx_call /\
    call_within H tops am_call tx_call es_call
End

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
       vfmExecutionPropTheory.all_accounts_def,
       vfmReturndataBoundTheory.returndata_bounded_def]
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
   (rw[global_cells_typed_def, vyperStateTheory.get_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> gvs[] >> EVAL_TAC) >>
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

val p23_src_call_eval = EVAL
  ``call_external (SOME []) gs p23_am_call p23_call_tx``;

val p23_dso_eval = REWRITE_RULE []
  (EVAL ``deploy_storage_ok p23_tops initial_machine_state p23_deploy_tx [] []``);

Theorem not_starved_on_success:
  ~frame_resource_starved es (INR NONE) es'
Proof
  simp[frame_resource_starved_def, frame_outcome_def] >>
  rpt gen_tac >> disj2_tac >> disj1_tac >> rpt strip_tac >>
  (namedCases_on `rest` ["", "parent_frame outer_frames"]
   >- gvs[] >>
   PairCases_on `parent_frame` >> gvs[])
QED

val p23_committed_code_eval = EVAL
  ``(lookup_account 2w
      (process_deletions p23_es_dep_post.rollback.toDelete
        p23_es_dep_post.rollback.accounts)).code =
      p23_runtime_bc ++ word_to_bytes (42w : bytes32) T``;

(* The call starts with no balance anywhere and no return data. *)
Theorem p23_call_bounds[local]:
  balance_bounded (2 ** 256 - 1) p23_es_call /\ returndata_bounded p23_es_call
Proof
  `vfmTotalBalance$total_balance
     (process_deletions p23_es_dep_post.rollback.toDelete
        p23_es_dep_post.rollback.accounts) = 0` by
    (simp[vfmTotalBalanceTheory.total_balance_def,
          pred_setTheory.SUM_IMAGE_ZERO] >>
     simp[p23_es_dep_post_def, vfmExecutionTheory.process_deletions_def,
          vfmStateTheory.lookup_account_def] >>
     qx_gen_tac `address` >> EVAL_TAC >>
     Cases_on `2w = address` >> simp[] >> EVAL_TAC) >>
  rewrite_tac[p23_es_call_from_post] >>
  simp[p23_es_call_of_def, LET_THM, vfmTotalBalanceTheory.balance_bounded_def,
       vfmReturndataBoundTheory.returndata_bounded_def,
       vfmExecutionPropTheory.all_accounts_def, p23_frame_def]
QED

Theorem p23_call_state:
  call_state_rel p23_tops p23_runtime_bc p23_am_call p23_call_tx p23_es_call
Proof
  rewrite_tac[call_state_rel_def, frame_fresh_def, frame_tx_rel_def,
              world_rel_def, evm_state_ok_def, p23_call_bounds] >>
  rewrite_tac[p23_es_call_from_post, p23_es_call_of_def] >>
  simp[LET_THM] >>
  simp[p23_frame_def, p23_call_tx_def, vyperContextTheory.empty_call_txn_def,
       p23_am_call_def, next_source_machine_def,
       value_transfer_ok_def, accounts_after_transfer_def,
       tx_block_fields_rel_def, p23_tx_params_def,
       loweringStateRelDefsTheory.tx_env_ok_def] >>
  simp[vfmExecutionPropTheory.wf_state_def,
       vfmExecutionPropTheory.wf_context_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmExecutionPropTheory.stack_room_ok_def,
       vfmExecutionPropTheory.gas_stack_ok_def,
       vfmExecutionPropTheory.outputTo_consistent_stack_def,
       vfmExecutionPropTheory.outputTo_consistent_ctx_def,
       vfmCalldataBoundTheory.calldata_bounded_def,
       vfmCalldataBoundTheory.memory_paid_def,
       vfmCalldataBoundTheory.frames_paid_def,
       vfmCalldataBoundTheory.outputs_fit_def,
       p23_get_calldata_def,
       account_immutables_def, source_deployment_rel_def,
       p23_am_dep_post_def, layouts_agree_def, p23_tops_def] >>
  rewrite_tac[EQT_ELIM p23_committed_code_eval] >>
  simp[p23_runtime_length_eval] >>
  conj_tac
  >- (simp[vfmExecutionPropTheory.wf_accounts_def,
           p23_es_dep_post_def, vfmExecutionTheory.process_deletions_def,
           vfmStateTheory.lookup_account_def,
           vfmExecutionPropTheory.wf_account_state_def] >>
      qx_gen_tac `address` >> EVAL_TAC >>
      Cases_on `2w = address` >> simp[] >> EVAL_TAC) >>
  rewrite_tac[immutableSectionRelTheory.installed_code_rel_def] >>
  conj_tac
  >- (simp[vfmStateTheory.account_empty_def, EQT_ELIM p23_committed_code_eval] >>
      EVAL_TAC) >>
  qexists_tac `word_to_bytes (42w : bytes32) T` >>
  simp[] >>
  mp_tac p23_immutables_section >>
  simp[account_immutables_def, p23_am_dep_post_def, p23_deploy_tx_def,
       vyperContextTheory.empty_call_txn_def, p23_tops_def]
QED


(* ===== Both conclusions on p23, and their guards ===== *)

Theorem p23_deploy_storage_ok:
  deploy_storage_ok p23_tops initial_machine_state p23_deploy_tx [] []
Proof
  simp[p23_dso_eval]
QED

Theorem gas_readings_rel_empty[local]:
  (!gs. P gs) ==> gas_readings_rel [] P
Proof
  strip_tac >> simp[gas_readings_rel_def] >>
  qexists `[]` >> simp[]
QED

val p23_dep_sources_eval =
  EVAL ``ALOOKUP p23_am_dep_post.sources p23_deploy_tx.target``;

(* The deployment's committed state, at ML top level: the tactic budget is
   too small to compute it inside a proof. *)
val p23_dep_code_eval = EVAL
  ``p23_runtime_bc ++ word_to_bytes (42w : bytes32) T =
    (lookup_account p23_deploy_tx.target p23_es_dep_post.rollback.accounts).code``;
val p23_dep_evm_accts = EVAL
  ``process_deletions p23_es_dep_post.rollback.toDelete
      (update_account p23_deploy_tx.target
         (lookup_account p23_deploy_tx.target p23_es_dep_post.rollback.accounts with
            code := (lookup_account p23_deploy_tx.target p23_am_dep_post.accounts).code)
         p23_es_dep_post.rollback.accounts)``;
val p23_dep_src_accts = EVAL ``p23_am_dep_post.accounts``;
val p23_dep_src_ts = EVAL ``p23_am_dep_post.tStorage``;
val p23_dep_evm_ts = EVAL ``p23_es_dep_post.rollback.tStorage``;

Theorem p23_deploy_result:
  deploy_call_result_rel p23_tops p23_runtime_bc initial_machine_state
    p23_deploy_tx p23_es_dep (INR NONE) p23_es_dep_post
Proof
  assume_tac p23_immutables_section >>
  simp[deploy_call_result_rel_def, p23_dep_trace] >>
  irule gas_readings_rel_empty >> simp[p23_load, deploy_result_rel_def] >>
  rpt strip_tac >> simp[p23_dep_sources_eval] >>
  qexists `word_to_bytes (42w:bytes32) T` >>
  conj_tac >- simp[] >>
  conj_tac >- (
    simp[frame_outcome_def, p23_es_dep_def, p23_frame_def,
         p23_es_dep_post_def, p23_am_dep_post_def] >>
    EVAL_TAC >> simp[vfmContextTheory.transaction_parameters_component_equality]) >>
  rewrite_tac[p23_dep_code_eval, p23_dep_evm_accts] >>
  rewrite_tac[p23_dep_src_accts, p23_dep_src_ts, p23_dep_evm_ts] >>
  simp[loweringStateRelDefsTheory.accounts_agree_def,
       loweringStateRelDefsTheory.storage_agree_def,
       loweringStateRelDefsTheory.transient_agree_def,
       call_requests_def, p23_dep_trace] >>
  simp[initial_evaluation_context_def, p23_deploy_tx_def,
       vyperContextTheory.empty_call_txn_def, vfmStateTheory.lookup_storage_def,
       vfmStateTheory.empty_accounts_def, vfmStateTheory.empty_account_state_def,
       vfmContextTheory.empty_transient_storage_def, combinTheory.APPLY_UPDATE_THM,
       vfmStateTheory.account_state_component_equality] >>
  rw[] >> simp[vfmStateTheory.empty_storage_def]
QED

Theorem p23_call_result:
  call_result_rel ([], []) p23_tops p23_am_call p23_call_tx
    p23_es_call (INR NONE) p23_es_call_post
Proof
  simp[call_result_rel_def, p23_call_trace] >>
  irule gas_readings_rel_empty >>
  simp[p23_src_call_eval, storage_ok_def, regions_consistent_def,
       storage_locks_separated_def, storage_well_formed_on_def] >>
  gen_tac >>
  simp[call_result_rel_at_def, p23_call_trace, LET_THM] >>
  simp[p23_src_call_eval, effects_agree_def] >> rpt strip_tac >>
  qexists `word_to_bytes (42w:bytes32) T` >>
  conj_tac >- (rewrite_tac[tx_return_bytes_def] >> EVAL_TAC >> simp[] >> EVAL_TAC) >>
  conj_tac >- (
    simp[frame_outcome_def, p23_es_call_from_post, p23_es_call_of_def,
         p23_frame_def, p23_es_call_post_def] >>
    EVAL_TAC >> simp[vfmContextTheory.transaction_parameters_component_equality]) >>
  simp[loweringStateRelDefsTheory.accounts_agree_def,
       loweringStateRelDefsTheory.storage_agree_def,
       loweringStateRelDefsTheory.transient_agree_def,
       p23_es_call_post_def, vfmContextTheory.empty_transient_storage_def,
       vfmStateTheory.empty_storage_def, call_requests_def, p23_call_trace] >>
  simp[vfmExecutionTheory.process_deletions_def, initial_evaluation_context_def,
       p23_call_tx_def, vfmStateTheory.account_state_component_equality]
QED

val p23_dispatch_eval = EVAL ``calldata_dispatch p23_tops p23_call_tx.calldata``;

Theorem p23_dispatched_tx[local]:
  p23_call_tx with <| function_name := "get"; args := [] |> = p23_call_tx
Proof
  simp[p23_call_tx_def, vyperContextTheory.empty_call_txn_def]
QED

Theorem p23_storage_ok[local]:
  storage_ok ([], []) p23_am_call p23_call_tx
Proof
  simp[storage_ok_def, regions_consistent_def, storage_locks_separated_def,
       storage_well_formed_on_def]
QED

val p23_storage_trace_eval =
  EVAL ``source_storage_trace p23_am_call p23_call_tx [] gobs``;

Theorem p23_call_within[local]:
  call_within ([], []) p23_tops p23_am_call p23_call_tx p23_es_call
Proof
  simp[call_within_def, p23_dispatch_eval, p23_dispatched_tx, p23_call_trace] >>
  simp[p23_storage_trace_eval, storage_observations_ok_def, storage_trace_regions_def,
       storage_trace_locks_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def]
QED

(* Check the live statements without storing their instances. *)
local
  val accepted = prove (``(K SOME) IN accepted_finalizers``,
    simp[asmOptimizerTheory.accepted_finalizers_def])
  val dep_bound = prove (``LENGTH (call_trace p23_es_dep) < 2 ** 64``,
    simp[p23_dep_trace])
  val call_bound = prove (``LENGTH (call_trace p23_es_call) < 2 ** 64``,
    simp[p23_call_trace])
  val call_premises = CONJUNCTS (REWRITE_RULE [call_premises_deployed]
    (CONJ p23_source_typing p23_call_state))
in
  val _ = MATCH_MP
    (Q.SPECL [`K SOME`, `o1_policy all_capabilities`, `p23_tops`,
      `p23_deploy_bc`, `p23_runtime_bc`, `initial_machine_state`,
      `p23_deploy_tx`, `p23_es_dep`] e2e_deploy_correctness_deployed)
    (LIST_CONJ [accepted, p23_compile, p23_deploy_typing, p23_deploy_state, dep_bound])
  val _ = MATCH_MP
    (Q.SPECL [`K SOME`, `o1_policy all_capabilities`, `p23_tops`,
      `p23_deploy_bc`, `p23_runtime_bc`, `p23_am_call`, `p23_call_tx`,
      `p23_es_call`, `([], [])`] vyper_call_correct_deployed)
    (LIST_CONJ ([accepted, p23_compile] @ call_premises @
                [call_bound, p23_storage_ok, p23_call_within]))
end

(* ===== The witness ===== *)

(* Neither frame reads gas, and the immutable getter needs no storage regions. *)
Theorem vyper_deploy_and_call_premises_jointly_satisfiable:
  ?fin policy tops deploy_bc runtime_bc am_dep tx_dep es_dep r_dep es_dep'
     am_dep' rqs_dep tx_call es_call r_call es_call' H.
    vyper_deploy_and_call_premises fin policy tops deploy_bc runtime_bc
      am_dep tx_dep es_dep (next_source_machine am_dep' es_dep')
      tx_call es_call H /\
    run_call es_dep = SOME (r_dep, es_dep') /\
    ~creation_resource_starved es_dep r_dep es_dep' /\
    gas_readings es_dep = [] /\
    deploy_storage_ok tops am_dep tx_dep (MAP SND (call_trace es_dep)) [] /\
    load_contract (SOME (MAP SND (call_trace es_dep))) [] am_dep tx_dep
      [(NONE, tops)] [] = INL (am_dep', rqs_dep) /\
    deploy_call_result_rel tops runtime_bc am_dep tx_dep es_dep r_dep es_dep' /\
    run_call es_call = SOME (r_call, es_call') /\
    ~frame_resource_starved es_call r_call es_call' /\
    gas_readings es_call = [] /\
    calldata_dispatch tops tx_call.calldata = SOME (tx_call.function_name, tx_call.args) /\
    calldata_result_rel H tops (next_source_machine am_dep' es_dep') tx_call
      es_call r_call es_call' /\
    FST (call_external (SOME []) [] (next_source_machine am_dep' es_dep')
           tx_call) = INL (IntV 42) /\
    (FST (HD es_call'.contexts)).returnData = word_to_bytes (42w : bytes32) T
Proof
  qexistsl [`K SOME`, `o1_policy all_capabilities`, `p23_tops`,
            `p23_deploy_bc`, `p23_runtime_bc`, `initial_machine_state`,
            `p23_deploy_tx`, `p23_es_dep`, `INR NONE`, `p23_es_dep_post`,
            `p23_am_dep_post`, `[]`, `p23_call_tx`, `p23_es_call`, `INR NONE`,
            `p23_es_call_post`, `([], [])`] >>
  REWRITE_TAC [GSYM p23_am_call_def, vyper_deploy_and_call_premises_def,
    p23_compile, p23_deploy_typing, p23_deploy_state, p23_source_typing,
    p23_call_state, p23_deploy_result,
    p23_dep_run, p23_call_run, p23_dep_trace, p23_call_trace,
    not_starved_on_success, p23_evm_return_42,
    p23_source_call_42, listTheory.MAP, p23_load,
    p23_deploy_storage_ok, p23_storage_ok, p23_call_within, p23_dispatch_eval] >>
  simp[asmOptimizerTheory.accepted_finalizers_def,
       calldata_result_rel_def, p23_dispatch_eval, p23_dispatched_tx,
       p23_call_result,
       creation_resource_starved_def, frame_outcome_def, p23_es_dep_def] >>
  simp[p23_call_tx_def, vyperContextTheory.empty_call_txn_def]
QED

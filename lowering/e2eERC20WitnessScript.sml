(* Concrete balances HashMap lifecycle: mint 100, transfer 7, retain 93. *)
Theory e2eERC20Witness
Ancestors
  e2eWitnessCompute e2eWitness e2eCompose e2eDefs e2eDeployDefs compileVyper venomPipelineDriver supportedProgram
  concretizeMemLocDefs codegenReadyCompute alist integer_word
  vyperInterpreter vyperHashMapStorage vfmCompute e2eLifecycle accountsRelProps
  callTrace frameOutcome asmOptimizer
Libs
  finite_mapLib computeLib cv_transLib wordsLib intReduce vyperCheckContractLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

Definition erc20_tops_def:
  erc20_tops =
    [HashMapDecl Private F "balances" (BaseT AddressT)
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
       [Assign
          (BaseTarget (SubscriptTarget
            (TopLevelNameTarget (NONE, "balances"))
            (Builtin (BaseT AddressT) (Env Sender) [])))
          (Literal (BaseT (UintT 256)) (IntL 100))];
     FunctionDecl External Nonpayable F F "transfer"
       [("to", BaseT AddressT); ("amount", BaseT (UintT 256))]
       [] (BaseT BoolT)
       [AugAssign (BaseT (UintT 256))
          (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
            (Builtin (BaseT AddressT) (Env Sender) []))
          Sub (Name (BaseT (UintT 256)) "amount");
        AugAssign (BaseT (UintT 256))
          (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
            (Name (BaseT AddressT) "to"))
          Add (Name (BaseT (UintT 256)) "amount");
        Return (SOME (Literal (BaseT BoolT) (BoolL T)))]]
End

val erc20_compile_eval =
  EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) erc20_tops``;

val (erc20_deploy_bytes, erc20_runtime_bytes) =
  pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl erc20_compile_eval)));

Definition erc20_deploy_bc_def:
  erc20_deploy_bc : word8 list = ^erc20_deploy_bytes
End

Definition erc20_runtime_bc_def:
  erc20_runtime_bc : word8 list = ^erc20_runtime_bytes
End

Theorem erc20_compile:
  compile_vyper (K SOME) (o1_policy all_capabilities) erc20_tops =
    SOME (erc20_deploy_bc, erc20_runtime_bc)
Proof
  PURE_REWRITE_TAC
    [erc20_compile_eval, erc20_deploy_bc_def, erc20_runtime_bc_def] >> REFL_TAC
QED


Definition erc20_initial_machine_def:
  erc20_initial_machine = initial_machine_state with
    layouts := [(2w, ([((NONE, "balances"), 0)], []))]
End

Definition erc20_deploy_tx_def:
  erc20_deploy_tx = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "__init__";
       code := erc20_deploy_bc;
       block_number := 1; block_hashes := [0w] |>
End

val erc20_transfer_calldata_eval = EVAL
  ``function_selector "transfer" [Address; Uint 256] ++
    enc (Tuple [Address; Uint 256]) (ListV [NumV 3; NumV 7])``;

Definition erc20_transfer_calldata_def:
  erc20_transfer_calldata : word8 list =
    ^(rhs (concl erc20_transfer_calldata_eval))
End

Theorem erc20_transfer_calldata_encodes:
  erc20_transfer_calldata =
    function_selector "transfer" [Address; Uint 256] ++
    enc (Tuple [Address; Uint 256]) (ListV [NumV 3; NumV 7])
Proof
  REWRITE_TAC [erc20_transfer_calldata_eval, erc20_transfer_calldata_def]
QED

Definition erc20_transfer_tx_def:
  erc20_transfer_tx = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "transfer";
       args := [AddressV 3w; IntV 7]; calldata := erc20_transfer_calldata;
       code := erc20_runtime_bc;
       block_number := 1; block_hashes := [0w] |>
End

val erc20_load_eval = EVAL
  ``load_contract (SOME []) gs erc20_initial_machine erc20_deploy_tx
    [(NONE, erc20_tops)] []``;

Definition erc20_am_dep_post_def:
  erc20_am_dep_post =
    ^(fst (pairSyntax.dest_pair
      (fst (sumSyntax.dest_inl (rhs (concl erc20_load_eval))))))
End

Theorem erc20_load:
  !gs. load_contract (SOME []) gs erc20_initial_machine erc20_deploy_tx
    [(NONE, erc20_tops)] [] = INL (erc20_am_dep_post, [])
Proof
  gen_tac >> PURE_REWRITE_TAC [erc20_load_eval, erc20_am_dep_post_def] >>
  REFL_TAC
QED

Definition erc20_es_dep_def:
  erc20_es_dep =
    <| contexts :=
         [(p23_frame erc20_deploy_bc [] (Code 2w), p23_dep_rollback)];
       txParams := p23_tx_params; rollback := p23_dep_rollback;
       originalAccounts := empty_accounts;
       msdomain := Collect empty_domain |>
End

val () = cv_auto_trans erc20_deploy_bc_def;
val () = cv_auto_trans erc20_runtime_bc_def;
val () = cv_auto_trans erc20_transfer_calldata_def;
val () = cv_auto_trans erc20_es_dep_def;

(* Retain the cv representation of states with hashed access-set keys. *)
val erc20_dep_run_eval = cv_eval_pat
  (cvSome (cvTuple [cvEval EVAL, cvName "erc20_es_dep_post"]))
  ``run_call erc20_es_dep``;

Theorem erc20_dep_run:
  run_call erc20_es_dep = SOME (INR NONE, erc20_es_dep_post)
Proof
  ACCEPT_TAC erc20_dep_run_eval
QED

val erc20_sender_slot_eval = EVAL
  ``hashmap_slot_for 0w (BaseT AddressT) (AddressV 1w)``;

Definition erc20_sender_slot_def:
  erc20_sender_slot : bytes32 = ^(rhs (concl erc20_sender_slot_eval))
End

Definition erc20_deployed_accounts_def:
  erc20_deployed_accounts = update_account 2w
    (empty_account_state with
      <| code := erc20_runtime_bc;
         storage := update_storage erc20_sender_slot 100w empty_storage |>)
    empty_accounts
End

val () = cv_auto_trans erc20_sender_slot_def;
val () = cv_auto_trans erc20_deployed_accounts_def;

val erc20_committed_accounts_eval = cv_eval
  ``process_deletions erc20_es_dep_post.rollback.toDelete
      erc20_es_dep_post.rollback.accounts = erc20_deployed_accounts``;

Definition erc20_am_call_def:
  erc20_am_call = next_source_machine erc20_am_dep_post erc20_es_dep_post
End

Theorem erc20_call_machine:
  erc20_am_call = erc20_am_dep_post with
    <| accounts := erc20_deployed_accounts;
       tStorage := empty_transient_storage;
       logs := []; pending_deletions := [] |>
Proof
  simp[erc20_am_call_def, next_source_machine_def,
       EQT_ELIM erc20_committed_accounts_eval]
QED

Definition erc20_es_transfer_def:
  erc20_es_transfer =
    let accts = process_deletions erc20_es_dep_post.rollback.toDelete
                  erc20_es_dep_post.rollback.accounts in
    let rb = erc20_es_dep_post.rollback with
      <| accounts := accts; tStorage := empty_transient_storage;
         toDelete := [] |> in
    <| contexts :=
         [(p23_frame (lookup_account 2w accts).code erc20_transfer_calldata
             (Memory <| offset := 0; size := 0 |>), rb)];
       txParams := p23_tx_params; rollback := rb;
       originalAccounts := accts; msdomain := Collect empty_domain |>
End

val () = cv_auto_trans erc20_es_transfer_def;

val erc20_transfer_run_eval = cv_eval_pat
  (cvSome (cvTuple [cvEval EVAL, cvName "erc20_es_transfer_post"]))
  ``run_call erc20_es_transfer``;

Theorem erc20_transfer_run:
  run_call erc20_es_transfer = SOME (INR NONE, erc20_es_transfer_post)
Proof
  ACCEPT_TAC erc20_transfer_run_eval
QED

val erc20_source_transfer_eval = (REWRITE_CONV [erc20_call_machine] THENC EVAL)
  ``call_external (SOME []) gs erc20_am_call erc20_transfer_tx``;

Definition erc20_am_transfer_post_def:
  erc20_am_transfer_post =
    ^(fst (pairSyntax.dest_pair
      (snd (pairSyntax.dest_pair (rhs (concl erc20_source_transfer_eval))))))
End

Theorem erc20_source_transfer:
  !gs. call_external (SOME []) gs erc20_am_call erc20_transfer_tx =
    (INL (BoolV T), erc20_am_transfer_post, [])
Proof
  gen_tac >>
  PURE_REWRITE_TAC [erc20_source_transfer_eval, erc20_am_transfer_post_def] >>
  REFL_TAC
QED

val erc20_dep_quiet = cv_eval
  ``frame_quiet_tr (LENGTH erc20_es_dep.contexts)
    erc20_es_dep (step erc20_es_dep)``;
val erc20_transfer_quiet = cv_eval
  ``frame_quiet_tr (LENGTH erc20_es_transfer.contexts)
    erc20_es_transfer (step erc20_es_transfer)``;

Theorem erc20_dep_trace:
  gas_readings erc20_es_dep = [] /\ call_trace erc20_es_dep = []
Proof
  irule frame_quiet_obs >> ACCEPT_TAC (EQT_ELIM erc20_dep_quiet)
QED

Theorem erc20_transfer_trace:
  gas_readings erc20_es_transfer = [] /\ call_trace erc20_es_transfer = []
Proof
  irule frame_quiet_obs >> ACCEPT_TAC (EQT_ELIM erc20_transfer_quiet)
QED

val erc20_guards_eval = (REWRITE_CONV [erc20_call_machine] THENC EVAL)
  ``deploy_storage_ok erc20_tops erc20_initial_machine erc20_deploy_tx [] [] /\
    source_storage_ok erc20_am_call erc20_transfer_tx [] [] /\
    call_outcomes_storage_ok erc20_am_call erc20_transfer_tx [] []``;

Theorem erc20_finite_guards:
  deploy_storage_ok erc20_tops erc20_initial_machine erc20_deploy_tx [] [] /\
  source_storage_ok erc20_am_call erc20_transfer_tx [] [] /\
  call_outcomes_storage_ok erc20_am_call erc20_transfer_tx [] []
Proof
  rewrite_tac[erc20_guards_eval] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >> EVAL_TAC
QED

val erc20_recipient_slot_eval = EVAL
  ``hashmap_slot_for 0w (BaseT AddressT) (AddressV 3w)``;

val erc20_balances_eval =
  (REWRITE_CONV [erc20_sender_slot_eval, erc20_recipient_slot_eval] THENC cv_eval)
  ``lookup_storage (hashmap_slot_for 0w (BaseT AddressT) (AddressV 1w))
      (lookup_account 2w erc20_es_transfer_post.rollback.accounts).storage = 93w /\
    lookup_storage (hashmap_slot_for 0w (BaseT AddressT) (AddressV 3w))
      (lookup_account 2w erc20_es_transfer_post.rollback.accounts).storage = 7w /\
    (case erc20_es_transfer_post.contexts of
       [] => F
     | (c, rb) :: rest => c.returnData = word_to_bytes (1w : bytes32) T)``;

Theorem erc20_transfer_balances:
  lookup_storage (hashmap_slot_for 0w (BaseT AddressT) (AddressV 1w))
    (lookup_account 2w erc20_es_transfer_post.rollback.accounts).storage = 93w /\
  lookup_storage (hashmap_slot_for 0w (BaseT AddressT) (AddressV 3w))
    (lookup_account 2w erc20_es_transfer_post.rollback.accounts).storage = 7w /\
  (FST (HD erc20_es_transfer_post.contexts)).returnData =
    word_to_bytes (1w : bytes32) T
Proof
  mp_tac (EQT_ELIM erc20_balances_eval) >>
  Cases_on `erc20_es_transfer_post.contexts` >> simp[] >>
  PairCases_on `h` >> simp[]
QED

val erc20_check_dep =
  (SIMP_CONV (srw_ss())
     [erc20_initial_machine_def, vyperInterpreterTheory.initial_machine_state_def,
      erc20_tops_def] THENC vyperCheckContractLib.check_contract_conv)
  ``check_contract T erc20_initial_machine.layouts 2w [(NONE, erc20_tops)]``;
val erc20_check_run =
  (SIMP_CONV (srw_ss())
     [erc20_initial_machine_def, vyperInterpreterTheory.initial_machine_state_def,
      erc20_tops_def] THENC vyperCheckContractLib.check_contract_conv)
  ``check_contract F erc20_initial_machine.layouts 2w [(NONE, erc20_tops)]``;
val erc20_check_dep_expanded = SIMP_RULE (srw_ss())
  [erc20_initial_machine_def, vyperInterpreterTheory.initial_machine_state_def]
  erc20_check_dep;
val erc20_check_run_expanded = SIMP_RULE (srw_ss())
  [erc20_initial_machine_def, vyperInterpreterTheory.initial_machine_state_def]
  erc20_check_run;
val erc20_initial_imms = EVAL
  ``initial_immutables (type_env_all_modules [(NONE, erc20_tops)])
    [(NONE, erc20_tops)]``;
val erc20_deploy_code_length = EVAL ``LENGTH erc20_deploy_bc``;
val erc20_runtime_code_length = EVAL ``LENGTH erc20_runtime_bc``;
val erc20_constants_eval = EVAL
  ``evaluate_all_constants
    (deploy_evaluation_context erc20_tops erc20_initial_machine erc20_deploy_tx)
    (erc20_initial_machine with
      <| immutables := [(2w, THE (initial_immutables
           (type_env_all_modules [(NONE, erc20_tops)]) [(NONE, erc20_tops)]))];
         exports := [(2w, [])] |>) 2w [(NONE, erc20_tops)]``;
val erc20_constants_expanded = SIMP_RULE (srw_ss())
  [erc20_initial_machine_def, vyperInterpreterTheory.initial_machine_state_def,
   erc20_deploy_tx_def, vyperContextTheory.empty_call_txn_def,
   erc20_initial_imms] erc20_constants_eval;

Theorem erc20_deploy_typing:
  deploy_typing_ok erc20_tops erc20_initial_machine erc20_deploy_tx
Proof
  simp[deploy_typing_ok_constants_ready, erc20_check_dep_expanded,
       erc20_check_run_expanded,
       erc20_initial_imms, erc20_deploy_tx_def,
       vyperContextTheory.empty_call_txn_def, erc20_deploy_code_length,
       erc20_initial_machine_def,
       vyperInterpreterTheory.initial_machine_state_def,
       vyperTypeInitialStateTheory.machine_well_typed_def,
       vyperTypeInvariantsTheory.accounts_well_typed_def,
       vyperTypeInvariantsTheory.account_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def,
       vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
       vyperTypeEntryReadinessTheory.checked_deployment_constants_ready_def] >>
  simp[erc20_constants_expanded,
       vyperTypeEntryReadinessTheory.deployment_constants_output_typed_def,
       vyperTypeInvariantsTheory.imms_well_typed_def, erc20_tops_def]
QED

val erc20_transfer_lookup = EVAL
  ``vyperInterpreter$lookup_function NONE "transfer" External erc20_tops``;

Theorem erc20_valid_transfer:
  valid_vyper_call erc20_tops erc20_transfer_tx erc20_transfer_calldata
    (BaseT BoolT)
Proof
  simp[valid_vyper_call_def, erc20_transfer_tx_def,
       vyperContextTheory.empty_call_txn_def, erc20_transfer_lookup,
       vyperInterpreterTheory.bind_arguments_def,
       selectorDispatchTheory.calldata_encodes_def,
       erc20_transfer_calldata_encodes, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes, dividesTheory.divides_def] >>
  EVAL_TAC
QED

val erc20_constructor_encoding = EVAL
  ``constructor_args_encode erc20_tops erc20_deploy_tx []``;
val erc20_deploy_env = EVAL
  ``tx_block_fields_rel erc20_deploy_tx p23_tx_params``;

Theorem erc20_deploy_state:
  deploy_state_rel erc20_tops erc20_deploy_bc erc20_initial_machine
    erc20_deploy_tx erc20_es_dep
Proof
  rewrite_tac[deploy_state_rel_def, erc20_constructor_encoding,
              erc20_deploy_env] >>
  qexistsl [`p23_frame erc20_deploy_bc [] (Code 2w)`,
            `p23_dep_rollback`, `[]`] >>
  rewrite_tac[erc20_constructor_encoding, erc20_deploy_env] >>
  simp[erc20_es_dep_def, p23_frame_def, p23_dep_rollback_def] >>
  simp[vfmExecutionPropTheory.wf_state_def,
       vfmExecutionPropTheory.wf_context_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmExecutionPropTheory.stack_room_ok_def,
       vfmExecutionPropTheory.gas_stack_ok_def,
       vfmExecutionPropTheory.outputTo_consistent_stack_def,
       vfmExecutionPropTheory.outputTo_consistent_ctx_def,
       vfmExecutionPropTheory.wf_accounts_def,
       vfmStateTheory.empty_accounts_def, erc20_initial_machine_def,
       erc20_deploy_tx_def, vyperContextTheory.empty_call_txn_def,
       vyperInterpreterTheory.initial_machine_state_def,
       value_transfer_ok_def, accounts_after_transfer_def] >>
  simp[layouts_agree_def, erc20_tops_def,
       vfmStateTheory.account_empty_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.empty_accounts_def, vfmStateTheory.empty_account_state_def,
       vyperInterpreterTheory.bind_arguments_def, listTheory.REV_DEF,
       tx_block_fields_rel_def, p23_tx_params_def,
       loweringStateRelDefsTheory.tx_env_ok_def,
       vfmTotalBalanceTheory.balance_bounded_def,
       vfmTotalBalanceTheory.total_balance_def, pred_setTheory.SUM_IMAGE_ZERO,
       vfmExecutionPropTheory.all_accounts_def] >>
  `SUM_IMAGE (\x : address. 0) UNIV = 0` by
    simp[pred_setTheory.SUM_IMAGE_ZERO] >> simp[]
QED

val erc20_dep_source_accounts = PURE_REWRITE_RULE
  [GSYM vfmStateTheory.update_account_def, GSYM vfmStateTheory.update_storage_def,
   GSYM vfmStateTheory.empty_storage_def]
  (EVAL ``erc20_am_dep_post.accounts``);
val erc20_call_source_accounts = PURE_REWRITE_RULE
  [GSYM vfmStateTheory.update_account_def, GSYM vfmStateTheory.update_storage_def,
   GSYM vfmStateTheory.empty_storage_def]
  (EVAL ``erc20_am_transfer_post.accounts``);
val erc20_dep_source_transient = EVAL ``erc20_am_dep_post.tStorage``;
val erc20_call_source_transient = EVAL ``erc20_am_transfer_post.tStorage``;
val erc20_dep_source_facts = EVAL
  ``ALOOKUP erc20_am_dep_post.sources 2w <> NONE /\
    erc20_am_dep_post.logs = []``;

Theorem erc20_immutables_section[local]:
  immutables_section_rel erc20_tops imms []
Proof
  rw[immutableSectionRelTheory.immutables_section_rel_def]
  >- EVAL_TAC >>
  `MEM (VariableDecl vis Immutable name ty slot) erc20_tops` by
    (qpat_x_assum `_ = erc20_tops` (SUBST1_TAC o SYM) >> simp[]) >>
  fs[erc20_tops_def]
QED

val erc20_dep_facts =
  (REWRITE_CONV [erc20_dep_source_accounts, erc20_dep_source_transient]
    THENC cv_eval)
  ``LENGTH erc20_es_dep_post.contexts = 1 /\
    erc20_es_dep_post.txParams = erc20_es_dep.txParams /\
    (case erc20_es_dep_post.contexts of
       [] => F
     | (c, rb) :: rest => c.returnData = erc20_runtime_bc /\ c.logs = []) /\
    (lookup_account 2w erc20_es_dep_post.rollback.accounts).code =
      erc20_runtime_bc /\
    process_deletions erc20_es_dep_post.rollback.toDelete
      (update_account 2w
        (lookup_account 2w erc20_es_dep_post.rollback.accounts with
          code := (lookup_account 2w erc20_am_dep_post.accounts).code)
        erc20_es_dep_post.rollback.accounts) = erc20_am_dep_post.accounts /\
    erc20_es_dep_post.rollback.tStorage = erc20_am_dep_post.tStorage /\
    ~MEM 2w erc20_es_dep_post.rollback.toDelete``;

val erc20_transfer_facts =
  (REWRITE_CONV [erc20_call_source_accounts, erc20_call_source_transient]
    THENC cv_eval)
  ``LENGTH erc20_es_transfer_post.contexts = 1 /\
    erc20_es_transfer_post.txParams = erc20_es_transfer.txParams /\
    (case erc20_es_transfer_post.contexts of
       [] => F
     | (c, rb) :: rest =>
         c.returnData = word_to_bytes (1w : bytes32) T /\ c.logs = []) /\
    process_deletions erc20_es_transfer_post.rollback.toDelete
      erc20_es_transfer_post.rollback.accounts = erc20_am_transfer_post.accounts /\
    erc20_es_transfer_post.rollback.tStorage = erc20_am_transfer_post.tStorage /\
    ~MEM 2w erc20_es_transfer_post.rollback.toDelete``;

Theorem erc20_deploy_result_at[local]:
  deploy_result_rel H erc20_tops erc20_runtime_bc erc20_deploy_tx
    erc20_es_dep (INR NONE) erc20_es_dep_post (INL (erc20_am_dep_post, []))
Proof
  assume_tac (EQT_ELIM erc20_dep_facts) >>
  assume_tac (EQT_ELIM erc20_dep_source_facts) >>
  simp[deploy_result_rel_def, erc20_deploy_tx_def,
       vyperContextTheory.empty_call_txn_def] >>
  simp[erc20_immutables_section, accounts_agree_refl, transient_agree_refl,
       call_requests_def, erc20_dep_trace] >>
  fs[frame_outcome_def, erc20_es_dep_def, p23_frame_def] >>
  Cases_on `erc20_es_dep_post.contexts` >> gvs[] >>
  PairCases_on `h` >> gvs[]
QED

Theorem erc20_deploy_result:
  deploy_call_result_rel erc20_tops erc20_runtime_bc erc20_initial_machine
    erc20_deploy_tx erc20_es_dep (INR NONE) erc20_es_dep_post
Proof
  simp[deploy_call_result_rel_def, erc20_dep_trace, gas_readings_rel_def] >>
  qexists `[]` >> simp[erc20_load, erc20_deploy_result_at]
QED

val erc20_transfer_source_logs = EVAL ``erc20_am_transfer_post.logs = []``;
val erc20_transfer_return = EVAL
  ``tx_return_bytes erc20_tops (BaseT BoolT) erc20_transfer_tx (BoolV T)
      (word_to_bytes (1w : bytes32) T)``;

Theorem erc20_call_result:
  call_result_rel erc20_tops (BaseT BoolT) erc20_am_call erc20_transfer_tx
    erc20_es_transfer (INR NONE) erc20_es_transfer_post
Proof
  assume_tac (EQT_ELIM erc20_transfer_facts) >>
  assume_tac (EQT_ELIM erc20_transfer_source_logs) >>
  simp[call_result_rel_def, erc20_transfer_trace, gas_readings_rel_def] >>
  qexists `[]` >> simp[] >> rpt strip_tac >>
  simp[call_result_rel_at_def, erc20_transfer_trace,
       erc20_source_transfer, call_success_rel_def] >>
  qexists `word_to_bytes (1w : bytes32) T` >>
  simp[erc20_transfer_return, accounts_agree_refl, transient_agree_refl,
       call_requests_def, erc20_transfer_trace] >>
  fs[frame_outcome_def, erc20_es_transfer_def, p23_frame_def] >>
  Cases_on `erc20_es_transfer_post.contexts` >> gvs[] >>
  PairCases_on `h` >> gvs[] >> EVAL_TAC
QED

Theorem erc20_call_bounds[local]:
  balance_bounded (2 ** 256 - 1) erc20_es_transfer /\
  returndata_bounded erc20_es_transfer
Proof
  `vfmTotalBalance$total_balance erc20_deployed_accounts = 0` by
    (simp[vfmTotalBalanceTheory.total_balance_def,
          pred_setTheory.SUM_IMAGE_ZERO,
          erc20_deployed_accounts_def, vfmStateTheory.update_account_def,
          vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def] >>
     gen_tac >> Cases_on `x = 2w` >>
     simp[vfmStateTheory.empty_account_state_def,
          vfmStateTheory.empty_accounts_def,
          combinTheory.APPLY_UPDATE_THM]) >>
  simp[erc20_es_transfer_def, EQT_ELIM erc20_committed_accounts_eval,
       LET_THM, vfmTotalBalanceTheory.balance_bounded_def,
       vfmReturndataBoundTheory.returndata_bounded_def,
       vfmExecutionPropTheory.all_accounts_def, p23_frame_def]
QED

Theorem erc20_call_state:
  call_state_rel erc20_tops erc20_runtime_bc erc20_am_call
    erc20_transfer_tx erc20_es_transfer
Proof
  rewrite_tac[call_state_rel_def, erc20_call_bounds] >>
  simp[erc20_es_transfer_def, EQT_ELIM erc20_committed_accounts_eval,
       LET_THM, erc20_call_machine, p23_frame_def, erc20_transfer_tx_def,
       vyperContextTheory.empty_call_txn_def, erc20_am_dep_post_def,
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
       account_immutables_def, source_deployment_rel_def,
       layouts_agree_def, erc20_runtime_code_length,
       erc20_deployed_accounts_def, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def] >>
  simp[vfmExecutionPropTheory.wf_accounts_def,
       vfmExecutionPropTheory.wf_account_state_def,
       immutableSectionRelTheory.installed_code_rel_def,
       erc20_immutables_section, erc20_runtime_code_length] >>
  rpt conj_tac >> rpt gen_tac >> Cases_on `2w = x` >> simp[] >>
  EVAL_TAC >> simp[]
QED

val erc20_supported = EVAL
  ``supported_program erc20_tops /\ supported_program_deploy erc20_tops``;
val erc20_dep_target = EVAL ``erc20_deploy_tx.target``;
val erc20_transfer_target = EVAL ``erc20_transfer_tx.target``;
val erc20_transfer_typed = EVAL ``call_tx_well_typed erc20_transfer_tx``;
val erc20_no_self_code = EVAL ``program_reads_self_code erc20_tops``;

Theorem erc20_deploy_ready:
  call_ready erc20_tops erc20_runtime_bc erc20_am_call 2w
Proof
  assume_tac (EQT_ELIM erc20_dep_facts) >>
  `balance_bounded (2 ** 256 - 1) erc20_es_dep` by
    metis_tac[erc20_deploy_state, deploy_state_rel_def] >>
  mp_tac (Q.INST
    [`tops` |-> `erc20_tops`, `am` |-> `erc20_initial_machine`,
     `tx` |-> `erc20_deploy_tx`, `deploy_bc` |-> `erc20_deploy_bc`,
     `runtime_bc` |-> `erc20_runtime_bc`, `es` |-> `erc20_es_dep`,
     `r` |-> `INR NONE`, `es'` |-> `erc20_es_dep_post`,
     `am'` |-> `erc20_am_dep_post`, `rqs` |-> `[]`, `H` |-> `([], [])`,
     `orc` |-> `SOME []`, `gs` |-> `[]`]
    (INST_TYPE [alpha |-> ``:256``] deploy_establishes_call_ready)) >>
  simp[erc20_deploy_typing, erc20_deploy_state, EQT_ELIM erc20_supported,
       erc20_dep_run, erc20_dep_target, erc20_load,
       erc20_deploy_result_at, GSYM erc20_am_call_def]
QED

Theorem erc20_transfer_ready:
  call_ready erc20_tops erc20_runtime_bc
    (next_source_machine erc20_am_transfer_post erc20_es_transfer_post) 2w
Proof
  assume_tac (EQT_ELIM erc20_transfer_facts) >>
  mp_tac (Q.INST
    [`tops` |-> `erc20_tops`, `runtime_bc` |-> `erc20_runtime_bc`,
     `am` |-> `erc20_am_call`, `tx` |-> `erc20_transfer_tx`,
     `es` |-> `erc20_es_transfer`, `r` |-> `INR NONE`,
     `es'` |-> `erc20_es_transfer_post`, `am'` |-> `erc20_am_transfer_post`,
     `res` |-> `INL (BoolV T)`, `rqs` |-> `[]`,
     `orc` |-> `SOME []`, `gobs` |-> `[]`]
    call_preserves_call_ready) >>
  simp[erc20_transfer_target, erc20_deploy_ready,
       EQT_ELIM erc20_transfer_typed, EQT_ELIM erc20_supported,
       erc20_call_state, erc20_call_bounds, erc20_transfer_run,
       erc20_source_transfer] >>
  simp[erc20_es_transfer_def, LET_THM, erc20_runtime_bc_def]
QED

Theorem erc20_deploy_transfer_lifecycle:
  vyper_deploy_and_call_premises (K SOME) (o1_policy all_capabilities)
    erc20_tops erc20_deploy_bc erc20_runtime_bc
    erc20_initial_machine erc20_deploy_tx erc20_es_dep
    (next_source_machine erc20_am_dep_post erc20_es_dep_post)
    erc20_transfer_tx (BaseT BoolT) erc20_es_transfer /\
  run_call erc20_es_dep = SOME (INR NONE, erc20_es_dep_post) /\
  load_contract (SOME []) [] erc20_initial_machine erc20_deploy_tx
    [(NONE, erc20_tops)] [] = INL (erc20_am_dep_post, []) /\
  deploy_storage_ok erc20_tops erc20_initial_machine erc20_deploy_tx [] [] /\
  deploy_call_result_rel erc20_tops erc20_runtime_bc erc20_initial_machine
    erc20_deploy_tx erc20_es_dep (INR NONE) erc20_es_dep_post /\
  call_ready erc20_tops erc20_runtime_bc
    (next_source_machine erc20_am_dep_post erc20_es_dep_post) 2w /\
  run_call erc20_es_transfer = SOME (INR NONE, erc20_es_transfer_post) /\
  gas_readings erc20_es_dep = [] /\ call_trace erc20_es_dep = [] /\
  gas_readings erc20_es_transfer = [] /\ call_trace erc20_es_transfer = [] /\
  source_storage_ok (next_source_machine erc20_am_dep_post erc20_es_dep_post)
    erc20_transfer_tx [] [] /\
  call_outcomes_storage_ok
    (next_source_machine erc20_am_dep_post erc20_es_dep_post)
    erc20_transfer_tx [] [] /\
  call_result_rel erc20_tops (BaseT BoolT)
    (next_source_machine erc20_am_dep_post erc20_es_dep_post)
    erc20_transfer_tx erc20_es_transfer (INR NONE) erc20_es_transfer_post /\
  call_external (SOME []) []
    (next_source_machine erc20_am_dep_post erc20_es_dep_post)
    erc20_transfer_tx = (INL (BoolV T), erc20_am_transfer_post, []) /\
  (FST (HD erc20_es_transfer_post.contexts)).returnData =
    word_to_bytes (1w : bytes32) T /\
  lookup_storage (hashmap_slot_for 0w (BaseT AddressT) (AddressV 1w))
    (lookup_account 2w erc20_es_transfer_post.rollback.accounts).storage = 93w /\
  lookup_storage (hashmap_slot_for 0w (BaseT AddressT) (AddressV 3w))
    (lookup_account 2w erc20_es_transfer_post.rollback.accounts).storage = 7w /\
  call_ready erc20_tops erc20_runtime_bc
    (next_source_machine erc20_am_transfer_post erc20_es_transfer_post) 2w
Proof
  `source_typing_ok erc20_tops erc20_am_call erc20_transfer_tx` by
    (mp_tac erc20_deploy_ready >>
     simp[call_ready_def] >>
     metis_tac[EQT_ELIM erc20_transfer_typed, erc20_transfer_target]) >>
  `buffer_to_list (FST (HD erc20_es_transfer.contexts)).msgParams.data =
     erc20_transfer_calldata` by
    simp[erc20_es_transfer_def, LET_THM, p23_frame_def] >>
  REWRITE_TAC [GSYM erc20_am_call_def, vyper_deploy_and_call_premises_def,
    erc20_compile, erc20_deploy_typing, erc20_deploy_state,
    erc20_call_state, erc20_valid_transfer, erc20_deploy_result,
    erc20_call_result, erc20_dep_run, erc20_transfer_run, erc20_load,
    erc20_deploy_ready, erc20_transfer_ready, erc20_source_transfer,
    erc20_dep_trace, erc20_transfer_trace, EQF_ELIM erc20_no_self_code] >>
  simp[erc20_finite_guards, erc20_transfer_balances,
       erc20_valid_transfer, call_outcomes_ok_def,
       accepted_finalizers_def, LET_THM]
QED

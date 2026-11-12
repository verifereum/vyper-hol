(* Milestone 7, Tier 1: one closed deploy-then-call run of a real compiled
 * contract in which every premise of the deploy and call top theorems holds
 * at once, and both conclusions hold, all by evaluation.
 *
 * Fixture: bytecode/immutables/oracle/p23_imm_uint256
 *   X: immutable(uint256)
 *   @deploy def __init__(): X = 42
 *   @external def get() -> uint256: return X
 *)
Theory e2eWitness
Ancestors
  compileVyper venomPipelineDriver asmOptimizer supportedProgram
  concretizeMemLocDefs codegenReadyCompute alist integer_word option
  e2eProducers e2eDefs e2eDeployDefs callTrace frameOutcome
  vyperInterpreter vfmCompute
Libs
  memoryStoreWitnessLib finite_mapLib cv_transLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../bytecode/immutables/oracle"]

(* The compset the repo's compile tests evaluate compile_vyper with
   (tests/create/createRawCompileTestScript.sml). *)
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

(* ===== The fixture and its compilation ===== *)

val p23_tops_tm = memoryStoreWitnessLib.program
  "../bytecode/immutables/oracle" "p23_imm_uint256"

Definition p23_tops_def:
  p23_tops = ^p23_tops_tm
End

(* Evaluated once outside any proof step, on the literal program as the
   compile tests do, then folded back onto p23_tops. *)
val p23_compile_eval =
  REWRITE_RULE [GSYM p23_tops_def]
    (EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) ^p23_tops_tm``);

val (p23_deploy_bytes, p23_runtime_bytes) =
  pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl p23_compile_eval)));

Definition p23_deploy_bc_def:
  p23_deploy_bc : word8 list = ^p23_deploy_bytes
End

Definition p23_runtime_bc_def:
  p23_runtime_bc : word8 list = ^p23_runtime_bytes
End

Theorem p23_compile:
  compile_vyper (K SOME) (o1_policy all_capabilities) p23_tops =
    SOME (p23_deploy_bc, p23_runtime_bc)
Proof
  PURE_REWRITE_TAC [p23_compile_eval, p23_deploy_bc_def, p23_runtime_bc_def] >>
  REFL_TAC
QED

(* ===== Concrete transactions and EVM states ===== *)

Definition p23_deploy_tx_def:
  p23_deploy_tx = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "__init__";
       block_number := 1; block_hashes := [0w] |>
End

val p23_get_calldata_eval =
  EVAL ``function_selector "get" [] ++ enc (Tuple []) (ListV [])``;

Definition p23_get_calldata_def:
  p23_get_calldata : word8 list = ^(rhs (concl p23_get_calldata_eval))
End

Theorem p23_get_calldata_encodes:
  p23_get_calldata = function_selector "get" [] ++ enc (Tuple []) (ListV [])
Proof
  REWRITE_TAC [p23_get_calldata_eval, p23_get_calldata_def]
QED

Definition p23_call_tx_def:
  p23_call_tx = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "get";
       calldata := p23_get_calldata;
       block_number := 1; block_hashes := [0w] |>
End

(* The block fields both transactions read: tx_block_fields_rel. *)
Definition p23_tx_params_def:
  p23_tx_params =
    <| origin := 0w; gasPrice := 0; baseFeePerGas := 0;
       baseFeePerBlobGas := 0; blockNumber := 1; blockTimeStamp := 0;
       blockCoinBase := 0w; blockGasLimit := 0; prevRandao := 0w;
       prevHashes := [0w]; blobHashes := []; chainId := 0;
       authRefund := 0 |>
End

Definition p23_frame_def:
  p23_frame code data out =
    <| stack := []; memory := empty_buffer; pc := 0; jumpDest := NONE;
       returnData := []; gasUsed := 0; addRefund := 0; subRefund := 0;
       logs := [];
       msgParams :=
         <| caller := 1w; callee := 2w; code := code;
            parsed := parse_code 0 FEMPTY code; value := 0;
            gasLimit := 1000000; data := buffer_of_list data;
            static := F; outputTo := out |> |>
End

Definition p23_dep_rollback_def:
  p23_dep_rollback =
    <| accounts := empty_accounts; tStorage := empty_transient_storage;
       accesses := <| addresses := fEMPTY; storageKeys := fEMPTY |>;
       toDelete := [] |>
End

(* One creation frame running the deploy code at the empty address 2w. *)
Definition p23_es_dep_def:
  p23_es_dep =
    <| contexts := [(p23_frame p23_deploy_bc [] (Code 2w), p23_dep_rollback)];
       txParams := p23_tx_params; rollback := p23_dep_rollback;
       originalAccounts := empty_accounts;
       msdomain := Collect empty_domain |>
End

(* The call frame after deployment es': the committed accounts (pending
 * deletions processed, target code installed), fresh transient storage. *)
Definition p23_es_call_of_def:
  p23_es_call_of es' =
    let accts = process_deletions es'.rollback.toDelete es'.rollback.accounts in
    let rb = es'.rollback with
               <| accounts := accts; tStorage := empty_transient_storage;
                  toDelete := [] |> in
      <| contexts :=
           [(p23_frame (lookup_account 2w accts).code p23_get_calldata
               (Memory <| offset := 0; size := 0 |>), rb)];
         txParams := p23_tx_params; rollback := rb;
         originalAccounts := accts;
         msdomain := Collect empty_domain |>
End

Definition p23_es_call_def:
  p23_es_call =
    case run_call p23_es_dep of
      SOME (r, es') => p23_es_call_of es'
    | NONE => p23_es_dep
End

(* ===== The observed call trace and gas readings, by cv evaluation ===== *)

(* frame_obs's observers read HD/EL of contexts and stacks, so its cv
   translation carries side conditions that hold only by EVM step facts.
   Instead, frame_quiet_tr walks the same steps as frame_obs_tr and checks
   that no step at the frame's own depth is a GAS read or an observable
   call: then the observer never records anything (frame_quiet_tr_obs). It
   is total, so cv evaluates it on the concrete runs. *)
Definition frame_quiet_tr_def:
  frame_quiet_tr d s (r, s') <=>
    (ISR r \/
     case s.contexts of
       [] => F
     | (c, rb) :: rest =>
         LENGTH s.contexts <> d \/
         (next_opcode c <> SOME Gas /\ ~observable_call c)) /\
    (if ISR r \/ LENGTH s'.contexts < d then T
     else frame_quiet_tr d s' (step s'))
Termination
  WF_REL_TAC `inv_image ($< LEX ($< LEX $<))
    (\(d, s, (r, s')).
      if ISR r \/ LENGTH s'.contexts < d then ((0:num), (0, 0))
      else (1, vfmDecreasesGas$contexts_weight 0 s'.contexts))` >>
  rpt gen_tac >>
  rename1 `step post` >>
  mp_tac (Q.SPEC `post` (REWRITE_RULE [vfmDecreasesGasTheory.decreases_gas_cred_def]
    vfmDecreasesGasTheory.decreases_gas_cred_step)) >>
  IF_CASES_TAC >- (
    rw[vfmDecreasesGasTheory.contexts_weight_def,
       vfmExecutionPropTheory.unused_gas_def] >>
    gvs[vfmExecutionTheory.step_def, vfmExecutionTheory.handle_def,
        vfmExecutionTheory.get_current_context_def,
        vfmExecutionTheory.bind_def, vfmExecutionTheory.fail_def] >>
    gvs[vfmExecutionTheory.handle_step_def, vfmExecutionTheory.reraise_def]) >>
  rw[] >> fs[pairTheory.LEX_DEF, pairTheory.UNCURRY] >>
  metis_tac[sumTheory.sum_CASES, sumTheory.ISL, sumTheory.ISR]
End

Theorem observe_quiet[local]:
  (ISR r \/
   case s.contexts of
     [] => F
   | (c, rb) :: rest =>
       LENGTH s.contexts <> d \/
       (next_opcode c <> SOME Gas /\ ~observable_call c)) /\
  obs.pending = NONE ==>
  observe d s (r, s') obs = obs
Proof
  Cases_on `r` >> simp[observe_def] >>
  Cases_on `s.contexts` >> simp[] >>
  PairCases_on `h` >> rw[] >> gvs[]
QED

Theorem frame_quiet_tr_obs:
  !d s x obs.
    frame_quiet_tr d s x /\ obs.pending = NONE ==>
    frame_obs_tr d obs s x = obs
Proof
  simp[pairTheory.FORALL_PROD] >>
  recInduct frame_quiet_tr_ind >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  `observe d s (r,s') obs = obs` by (
    irule observe_quiet >> asm_rewrite_tac[] >>
    qpat_x_assum `frame_quiet_tr _ _ _` mp_tac >>
    PURE_ONCE_REWRITE_TAC [frame_quiet_tr_def] >>
    rpt strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `frame_quiet_tr _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [frame_quiet_tr_def] >>
  strip_tac >>
  PURE_ONCE_REWRITE_TAC [frame_obs_tr_def] >>
  asm_simp_tac std_ss [LET_THM] >>
  Cases_on `ISR r \/ LENGTH s'.contexts < d` >> gvs[]
QED

Theorem frame_quiet_obs:
  frame_quiet_tr (LENGTH es.contexts) es (step es) ==>
  gas_readings es = [] /\ call_trace es = []
Proof
  strip_tac >>
  `frame_obs es = <| entries := []; readings := []; pending := NONE |>`
    by (simp[frame_obs_def] >> irule frame_quiet_tr_obs >> simp[]) >>
  simp[gas_readings_def, call_trace_def]
QED

val () = cv_auto_trans next_opcode_def;
val () = cv_auto_trans observable_call_def;
(* The precondition only records the recursion; it holds by its induction,
   as vfmCompute's run_call_tr_pre. *)
val frame_quiet_tr_pre_def = cv_trans_pre "frame_quiet_tr_pre" frame_quiet_tr_def;

Theorem frame_quiet_tr_pre[cv_pre]:
  !d s x. frame_quiet_tr_pre d s x
Proof
  simp[pairTheory.FORALL_PROD] >>
  recInduct frame_quiet_tr_ind >> rw[] >>
  rw[Once frame_quiet_tr_pre_def]
QED

val () = cv_auto_trans p23_deploy_bc_def;
val () = cv_auto_trans p23_runtime_bc_def;
val () = cv_auto_trans p23_tx_params_def;
val () = cv_auto_trans p23_frame_def;
val () = cv_auto_trans p23_dep_rollback_def;
val () = cv_auto_trans p23_es_dep_def;
val () = cv_auto_trans p23_get_calldata_def;
val () = cv_auto_trans p23_es_call_of_def;
val () = cv_auto_trans p23_es_call_def;

(* ===== The concrete runs, evaluated once at top level ===== *)

val p23_dep_run_eval = cv_eval ``run_call p23_es_dep``;

Definition p23_es_dep_post_def:
  p23_es_dep_post =
    ^(snd (pairSyntax.dest_pair
            (optionSyntax.dest_some (rhs (concl p23_dep_run_eval)))))
End

Theorem p23_dep_run:
  run_call p23_es_dep = SOME (INR NONE, p23_es_dep_post)
Proof
  PURE_REWRITE_TAC [p23_dep_run_eval, p23_es_dep_post_def] >> REFL_TAC
QED

Theorem p23_es_call_from_post:
  p23_es_call = p23_es_call_of p23_es_dep_post
Proof
  simp[p23_es_call_def, p23_dep_run]
QED

val p23_call_run_eval = cv_eval ``run_call p23_es_call``;

Definition p23_es_call_post_def:
  p23_es_call_post =
    ^(snd (pairSyntax.dest_pair
            (optionSyntax.dest_some (rhs (concl p23_call_run_eval)))))
End

Theorem p23_call_run:
  run_call p23_es_call = SOME (INR NONE, p23_es_call_post)
Proof
  PURE_REWRITE_TAC [p23_call_run_eval, p23_es_call_post_def] >> REFL_TAC
QED

val p23_dep_quiet = cv_eval
  ``frame_quiet_tr (LENGTH p23_es_dep.contexts) p23_es_dep (step p23_es_dep)``;
val p23_call_quiet = cv_eval
  ``frame_quiet_tr (LENGTH p23_es_call.contexts) p23_es_call (step p23_es_call)``;

Theorem p23_dep_trace:
  gas_readings p23_es_dep = [] /\ call_trace p23_es_dep = []
Proof
  irule frame_quiet_obs >> ACCEPT_TAC (EQT_ELIM p23_dep_quiet)
QED

Theorem p23_call_trace:
  gas_readings p23_es_call = [] /\ call_trace p23_es_call = []
Proof
  irule frame_quiet_obs >> ACCEPT_TAC (EQT_ELIM p23_call_quiet)
QED

Theorem not_starved_on_success:
  ~frame_resource_starved es (INR NONE) es'
Proof
  simp[frame_resource_starved_def, frame_outcome_def] >>
  rpt gen_tac >> disj2_tac >> rpt strip_tac >>
  Cases_on `rest` >> TRY (PairCases_on `h`) >> gvs[]
QED

(* The source deployment, on the deploy frame's (empty) callee outcomes,
   never reads its gas list (no msg.gas). *)
val p23_load_eval = EVAL
  ``load_contract (SOME []) gs initial_machine_state p23_deploy_tx
      [(NONE, p23_tops)] []``;

Definition p23_am_dep_post_def:
  p23_am_dep_post =
    ^(fst (pairSyntax.dest_pair
            (fst (sumSyntax.dest_inl (rhs (concl p23_load_eval))))))
End

Theorem p23_load:
  !gs. load_contract (SOME []) gs initial_machine_state p23_deploy_tx
         [(NONE, p23_tops)] [] = INL (p23_am_dep_post, [])
Proof
  gen_tac >> PURE_REWRITE_TAC [p23_load_eval, p23_am_dep_post_def] >>
  REFL_TAC
QED

(* The source machine the call starts from. *)
Definition p23_am_call_def:
  p23_am_call = next_source_machine p23_am_dep_post p23_es_dep_post
End

val p23_src_call_eval = EVAL
  ``call_external (SOME []) gs p23_am_call p23_call_tx``;

val p23_src_call_42 = EVAL
  ``FST (call_external (SOME []) [] p23_am_call p23_call_tx) = INL (IntV 42)``;

val p23_return_42 = EVAL
  ``(FST (HD p23_es_call_post.contexts)).returnData =
    word_to_bytes (42w : bytes32) T``;

val p23_no_self_code = EVAL ``program_reads_self_code p23_tops``;
val p23_supported = EVAL ``supported_program p23_tops``;



val p23_dso_eval = REWRITE_RULE []
  (EVAL ``deploy_storage_ok p23_tops initial_machine_state p23_deploy_tx [] []``);

val p23_call_guard_eval = REWRITE_RULE []
  (EVAL ``source_storage_ok p23_am_call p23_call_tx [] [] /\
          call_outcomes_storage_ok p23_am_call p23_call_tx [] []``);

val p23_ccf_eval = SIMP_RULE (srw_ss())
  [supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
   supportedStmtTraverseTheory.supported_assignment_exists_def,
   supportedExprTraverseTheory.supported_expr_exists_def,
   constructor_call_root_def] (EVAL ``constructor_call_free p23_tops``);

(* The call frame's calldata, without unfolding the deploy run. *)
Theorem p23_call_data:
  buffer_to_list (FST (HD p23_es_call.contexts)).msgParams.data =
    p23_get_calldata
Proof
  simp[p23_es_call_from_post, p23_es_call_of_def, p23_frame_def]
QED

(* ===== The premises of both top theorems, as one conjunction ===== *)

(* The premises of the two top theorems on one compiled program, its
 * deployment (am_dep, tx_dep, es_dep) and the call that follows it
 * (am_call, tx_call, es_call), in the final text the definitions of
 * deploy-final a197306f0 state:
 *   deploy side: e2eDeployCorrectness.e2e_deploy_correctness;
 *   call side:   e2eCorrectness.vyper_call_correct.
 * - no supported_program / constructor_call_free / immutable_free_program:
 *   removed by the whitelist sign-off (Ramana, 2026-11-06).
 * - no ~(?t. runtime_bc = 0xEFw :: t): compile_vyper_runtime_not_ef proves
 *   it (seq-4132).
 * - deploy_storage_ok and source_storage_ok / call_outcomes_storage_ok are
 *   not premises: they are the finite-storage guards inside
 *   deploy_call_result_rel and call_result_rel (Ramana's finite-storage
 *   ruling); the witness shows they hold at the gas filling that matters.
 * - call_outcomes_ok on both frames' outcomes, as the tops state it. *)
Definition vyper_deploy_and_call_premises_def:
  vyper_deploy_and_call_premises fin policy tops deploy_bc runtime_bc
      am_dep tx_dep es_dep am_call tx_call ret es_call <=>
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    (* deploy *)
    deploy_typing_ok tops am_dep tx_dep /\
    deploy_state_rel tops deploy_bc am_dep tx_dep es_dep /\
    call_outcomes_ok am_dep tx_dep (MAP SND (call_trace es_dep)) /\
    (* call *)
    source_typing_ok tops am_call tx_call /\
    call_state_rel tops runtime_bc am_call tx_call es_call /\
    valid_vyper_call tops tx_call
      (buffer_to_list (FST (HD es_call.contexts)).msgParams.data) ret /\
    call_outcomes_ok am_call tx_call (MAP SND (call_trace es_call))
End

(* ===== The premises on p23, one by one ===== *)

val p23_check_dep = EVAL ``check_contract T [] 2w [(NONE, p23_tops)]``;
val p23_check_run = EVAL ``check_contract F [] 2w [(NONE, p23_tops)]``;
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
       vfmTotalBalanceTheory.balance_bounded_def, p23_total_balance_empty]
QED

val p23_exports_eval = EVAL ``exports_ok [] 2w [(NONE,p23_tops)] []``;
val p23_exports_eval_expanded = REWRITE_RULE
  [vyperTypeContractTheory.exports_ok_def,p23_tops_def] p23_exports_eval;
val p23_call_machine_eval = EVAL ``p23_am_call``;

Theorem p23_source_typing:
  source_typing_ok p23_tops p23_am_call p23_call_tx
Proof
  simp[source_typing_ok_def, p23_call_machine_eval, p23_call_tx_def,
       vyperContextTheory.empty_call_txn_def, p23_check_run,
       vyperTypeContractSoundnessTheory.checked_contract_runtime_ready_def,
       vyperTypeInitialStateTheory.machine_well_typed_def] >>
  simp[p23_tops_def, vyperTypeContractTheory.exports_ok_def,
       vyperTypeContractTheory.var_allocated_def,
       vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
       p23_get_calldata_def] >>
  simp[p23_exports_eval_expanded] >>
  conj_tac >- (simp[vyperTypeInitialStateTheory.immutables_ready_def,
                         finite_mapTheory.FLOOKUP_UPDATE,
       vyperInterpreterTheory.initial_evaluation_context_def,
       vyperStateTheory.get_source_immutables_def,
       vyperStateTheory.find_var_decl_by_name_def,
       vyperValueTheory.evaluate_type_def] >>
    simp[vyperContextTheory.get_module_code_def] >> rpt strip_tac >>
    gvs[vyperStateTheory.find_var_decl_by_name_def]) >>
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

val p23_call_context_eval = EVAL
  ``initial_evaluation_context p23_am_call.sources p23_am_call.layouts
      p23_call_tx NONE``;

Theorem p23_source_storage:
  source_storage_ok p23_am_call p23_call_tx [] [] /\
  call_outcomes_storage_ok p23_am_call p23_call_tx [] []
Proof
  ACCEPT_TAC p23_call_guard_eval
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
  qexistsl [`BaseTV (UintT 256)`, `IntV 42`] >> EVAL_TAC
QED

val p23_committed_code_eval = EVAL
  ``(lookup_account 2w
      (process_deletions p23_es_dep_post.rollback.toDelete
        p23_es_dep_post.rollback.accounts)).code =
      p23_runtime_bc ++ word_to_bytes (42w : bytes32) T``;
val p23_runtime_length_eval = EVAL ``LENGTH p23_runtime_bc``;

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
     gen_tac >> EVAL_TAC >> Cases_on `2w = x` >> simp[] >> EVAL_TAC) >>
  rewrite_tac[p23_es_call_from_post] >>
  simp[p23_es_call_of_def, LET_THM, vfmTotalBalanceTheory.balance_bounded_def,
       vfmReturndataBoundTheory.returndata_bounded_def,
       vfmExecutionPropTheory.all_accounts_def, p23_frame_def]
QED

Theorem p23_call_state:
  call_state_rel p23_tops p23_runtime_bc p23_am_call p23_call_tx p23_es_call
Proof
  rewrite_tac[call_state_rel_def, p23_call_bounds] >>
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
       account_immutables_def, source_deployment_rel_def,
       p23_am_dep_post_def, layouts_agree_def, p23_tops_def] >>
  rewrite_tac[EQT_ELIM p23_committed_code_eval] >>
  simp[p23_runtime_length_eval] >>
  conj_tac
  >- (simp[vfmExecutionPropTheory.wf_accounts_def,
           p23_es_dep_post_def, vfmExecutionTheory.process_deletions_def,
           vfmStateTheory.lookup_account_def,
           vfmExecutionPropTheory.wf_account_state_def] >>
      gen_tac >> EVAL_TAC >> Cases_on `2w = x` >> simp[] >> EVAL_TAC) >>
  rewrite_tac[immutableSectionRelTheory.installed_code_rel_def] >>
  qexists_tac `word_to_bytes (42w : bytes32) T` >>
  simp[] >>
  mp_tac p23_immutables_section >>
  simp[account_immutables_def, p23_am_dep_post_def, p23_deploy_tx_def,
       vyperContextTheory.empty_call_txn_def, p23_tops_def]
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

Theorem p23_constructor_call_free:
  constructor_call_free p23_tops
Proof
  ACCEPT_TAC p23_ccf_eval
QED

(* ===== Both conclusions on p23, and their guards ===== *)

Theorem p23_deploy_storage_ok:
  deploy_storage_ok p23_tops initial_machine_state p23_deploy_tx [] []
Proof
  ACCEPT_TAC p23_dso_eval
QED

Theorem gas_readings_rel_empty[local]:
  (!gs. f gs = out) ==> gas_readings_rel [] f out
Proof
  strip_tac >> simp[gas_readings_rel_def] >>
  qexists `[]` >> simp[]
QED

Theorem p23_deploy_result:
  deploy_call_result_rel p23_tops p23_runtime_bc initial_machine_state
    p23_deploy_tx p23_es_dep (INR NONE) p23_es_dep_post
Proof
  assume_tac p23_immutables_section >>
  simp[deploy_call_result_rel_def, p23_dep_trace] >>
  irule gas_readings_rel_empty >> simp[p23_load, deploy_result_rel_def] >>
  rpt strip_tac >> qexists `word_to_bytes (42w:bytes32) T` >>
  conj_tac >- simp[] >>
  conj_tac >- (
    simp[frame_outcome_def, p23_es_dep_def, p23_frame_def,
         p23_es_dep_post_def, p23_am_dep_post_def] >>
    EVAL_TAC >> simp[vfmContextTheory.transaction_parameters_component_equality]) >>
  simp[loweringStateRelDefsTheory.accounts_agree_def,
       loweringStateRelDefsTheory.storage_agree_def,
       loweringStateRelDefsTheory.transient_agree_def,
       vfmStateTheory.update_account_def,
       p23_am_dep_post_def, p23_es_dep_post_def, p23_deploy_tx_def,
       initial_evaluation_context_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.empty_accounts_def, vfmStateTheory.empty_account_state_def,
       vfmContextTheory.empty_transient_storage_def, combinTheory.APPLY_UPDATE_THM,
       vfmStateTheory.account_state_component_equality] >>
  EVAL_TAC >> simp[]
QED

Theorem p23_call_result:
  call_result_rel p23_tops (BaseT (UintT 256)) p23_am_call p23_call_tx
    p23_es_call (INR NONE) p23_es_call_post
Proof
  simp[call_result_rel_def, p23_call_trace] >>
  irule gas_readings_rel_empty >>
  simp[p23_src_call_eval, call_success_rel_def] >>
  qexists `word_to_bytes (42w:bytes32) T` >>
  conj_tac >- (
    simp[frame_outcome_def, p23_es_call_from_post, p23_es_call_of_def,
         p23_frame_def, p23_es_call_post_def] >>
    EVAL_TAC >> simp[vfmContextTheory.transaction_parameters_component_equality]) >>
  conj_tac >- (EVAL_TAC >> simp[] >> EVAL_TAC) >>
  simp[loweringStateRelDefsTheory.accounts_agree_def,
       loweringStateRelDefsTheory.storage_agree_def,
       loweringStateRelDefsTheory.transient_agree_def,
       p23_es_call_post_def, vfmContextTheory.empty_transient_storage_def,
       vfmStateTheory.empty_storage_def, call_requests_def, p23_call_trace] >>
  simp[vfmExecutionTheory.process_deletions_def, initial_evaluation_context_def,
       p23_call_tx_def, vfmStateTheory.account_state_component_equality]
QED

(* ===== The witness ===== *)

(* One closed deploy-then-call run of p23_imm_uint256 in which every
 * premise of both top theorems holds at once, both conclusions hold, the
 * only gas filling that matters ([]: neither run reads GAS) meets both
 * runs' finite-storage guards, and the call returns 42. *)
Theorem vyper_deploy_and_call_premises_jointly_satisfiable:
  ?fin policy tops deploy_bc runtime_bc am_dep tx_dep es_dep r_dep es_dep'
     am_dep' rqs_dep tx_call ret es_call r_call es_call'.
    vyper_deploy_and_call_premises fin policy tops deploy_bc runtime_bc
      am_dep tx_dep es_dep (next_source_machine am_dep' es_dep') tx_call ret
      es_call /\
    supported_program tops /\ constructor_call_free tops /\
    run_call es_dep = SOME (r_dep, es_dep') /\
    ~frame_resource_starved es_dep r_dep es_dep' /\
    gas_readings es_dep = [] /\
    deploy_storage_ok tops am_dep tx_dep (MAP SND (call_trace es_dep)) [] /\
    load_contract (SOME (MAP SND (call_trace es_dep))) [] am_dep tx_dep
      [(NONE, tops)] [] = INL (am_dep', rqs_dep) /\
    deploy_call_result_rel tops runtime_bc am_dep tx_dep es_dep r_dep es_dep' /\
    run_call es_call = SOME (r_call, es_call') /\
    ~frame_resource_starved es_call r_call es_call' /\
    gas_readings es_call = [] /\
    source_storage_ok (next_source_machine am_dep' es_dep') tx_call
      (MAP SND (call_trace es_call)) [] /\
    call_outcomes_storage_ok (next_source_machine am_dep' es_dep') tx_call
      (MAP SND (call_trace es_call)) [] /\
    call_result_rel tops ret (next_source_machine am_dep' es_dep') tx_call
      es_call r_call es_call' /\
    FST (call_external (SOME []) [] (next_source_machine am_dep' es_dep')
           tx_call) = INL (IntV 42) /\
    (FST (HD es_call'.contexts)).returnData = word_to_bytes (42w : bytes32) T
Proof
  qexistsl [`K SOME`, `o1_policy all_capabilities`, `p23_tops`,
            `p23_deploy_bc`, `p23_runtime_bc`, `initial_machine_state`,
            `p23_deploy_tx`, `p23_es_dep`, `INR NONE`, `p23_es_dep_post`,
            `p23_am_dep_post`, `[]`, `p23_call_tx`, `BaseT (UintT 256)`,
            `p23_es_call`, `INR NONE`, `p23_es_call_post`] >>
  REWRITE_TAC [GSYM p23_am_call_def, vyper_deploy_and_call_premises_def,
    p23_compile, p23_deploy_typing, p23_deploy_state, p23_source_typing,
    p23_source_storage, p23_call_state, p23_call_data, p23_valid_call,
    p23_constructor_call_free, p23_deploy_storage_ok, p23_deploy_result,
    p23_call_result, p23_dep_run, p23_call_run, p23_load,
    not_starved_on_success, p23_dep_trace, p23_call_trace,
    EQT_ELIM p23_supported, EQT_ELIM p23_src_call_42,
    EQT_ELIM p23_return_42,
    EQF_ELIM p23_no_self_code, call_outcomes_ok_def, listTheory.MAP, listTheory.EVERY_DEF] >>
  simp[accepted_finalizers_def]
QED

(* Deploy and call a linked unit with module-qualified storage and immutables. *)
Theory e2eModsWitness
Ancestors
  e2eWitnessCompute e2eModsDefs e2eDeployModsDefs
  compileUnit asmOptimizer jsonToVyper alist integer_word
Libs
  jsonASTLib vyperConstEvalLib vyperCheckContractLib
  computeLib finite_mapLib wordsLib intReduce cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../bytecode/linked-units/oracle/twin_names_locked.json"]

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

(* Use the import map to qualify storage keys and immutable offsets. *)
local
  val path = "../bytecode/linked-units/oracle/twin_names_locked.json"
  val ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path
  val layout = JSONDecode.decodeFile jsonASTLib.storage_layout path
  val translated = optionSyntax.dest_some
    (rhs (concl (EVAL ``translate_annotated_ast ^ast``)))
  val (sources, exports_and_imports) = pairSyntax.dest_pair translated
  val (exports, imports) = pairSyntax.dest_pair exports_and_imports
in
  val linked_mods = rhs (concl
    (EVAL ``annotate_sources_slots_mods ^layout ^imports ^sources``))
  val linked_exports = exports
  val linked_layout = rhs (concl (EVAL ``extract_storage_layout ^imports ^layout``))
  val lib_id = snd (pairSyntax.dest_pair (hd (#1 (listSyntax.dest_list exports))))
end

Definition linked_witness_mods_def:
  linked_witness_mods = ^linked_mods
End

Definition linked_witness_exports_def:
  linked_witness_exports = ^linked_exports
End

val () = computeLib.add_funs (map cv_eval [
  ``vyperABIEntries$abi_method_id FEMPTY "bar" []``,
  ``vyperABIEntries$abi_method_id FEMPTY "get_x" []``,
  ``vyperABIEntries$abi_method_id FEMPTY "locked_get_x" []``]);

(* Evaluate the whole compiler on the fixture. *)
val linked_compile_eval =
  CONV_RULE (RAND_CONV
    (PURE_ONCE_REWRITE_CONV [GSYM wordsTheory.n2w_mod] THENC
     DEPTH_CONV wordsLib.SIZES_CONV THENC numLib.REDUCE_CONV))
    (EVAL ``compile_vyper_mods asm_opt_finalizer
      (o1_policy all_capabilities) linked_witness_mods linked_witness_exports``)

val (linked_deploy_bytes, linked_runtime_bytes) =
  pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl linked_compile_eval)))

Definition linked_witness_deploy_bc_def:
  linked_witness_deploy_bc : word8 list = ^linked_deploy_bytes
End

Definition linked_witness_runtime_bc_def:
  linked_witness_runtime_bc : word8 list = ^linked_runtime_bytes
End

Triviality linked_witness_compile:
  compile_vyper_mods asm_opt_finalizer (o1_policy all_capabilities)
    linked_witness_mods linked_witness_exports =
    SOME (linked_witness_deploy_bc, linked_witness_runtime_bc)
Proof
  PURE_REWRITE_TAC [linked_compile_eval, linked_witness_deploy_bc_def,
                    linked_witness_runtime_bc_def] >>
  REFL_TAC
QED

Definition linked_witness_initial_machine_def:
  linked_witness_initial_machine = initial_machine_state with
    layouts := [(2w, ^linked_layout)]
End

Definition linked_witness_deploy_tx_def:
  linked_witness_deploy_tx = p23_deploy_tx with code := linked_witness_deploy_bc
End

Definition linked_witness_es_deploy_def:
  linked_witness_es_deploy = p23_es_dep with contexts :=
    [(p23_frame linked_witness_deploy_bc [] (Code 2w), p23_dep_rollback)]
End

val () = cv_auto_trans linked_witness_deploy_bc_def
val () = cv_auto_trans linked_witness_runtime_bc_def
val () = cv_auto_trans linked_witness_es_deploy_def

val linked_deploy_trace = MATCH_MP frame_quiet_obs (EQT_ELIM (cv_eval
  ``frame_quiet_tr (LENGTH linked_witness_es_deploy.contexts)
     linked_witness_es_deploy (step linked_witness_es_deploy)``))

val linked_ctor_encoding = EVAL
  ``constructor_args_encode_mods linked_witness_mods linked_witness_deploy_tx []``
val linked_deploy_env = EVAL
  ``tx_block_fields_rel linked_witness_deploy_tx p23_tx_params``
val linked_deploy_length = EVAL ``LENGTH linked_witness_deploy_bc``

val linked_check = SIMP_CONV (srw_ss())
  [linked_witness_initial_machine_def, vyperInterpreterTheory.initial_machine_state_def,
   linked_witness_mods_def, linked_witness_deploy_tx_def, p23_deploy_tx_def,
   vyperContextTheory.empty_call_txn_def] THENC
  vyperCheckContractLib.check_contract_conv

val linked_check_deploy =
  linked_check ``check_contract T linked_witness_initial_machine.layouts
    linked_witness_deploy_tx.target linked_witness_mods``
val linked_check_runtime =
  linked_check ``check_contract F linked_witness_initial_machine.layouts
    linked_witness_deploy_tx.target linked_witness_mods``

val empty_accounts_simps = [
  vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
  vfmStateTheory.empty_account_state_def]
val type_simps = [
  vyperTypeInitialStateTheory.machine_well_typed_def,
  vyperTypeInvariantsTheory.accounts_well_typed_def,
  vyperTypeInvariantsTheory.account_well_typed_def,
  vyperTypeInvariantsTheory.imms_well_typed_def,
  vyperTypeContractSoundnessTheory.call_tx_well_typed_def]
val frame_wf_simps = [
  vfmExecutionPropTheory.wf_state_def, vfmExecutionPropTheory.wf_context_def,
  vfmExecutionPropTheory.all_accounts_def,
  vfmExecutionPropTheory.stack_room_ok_def, vfmExecutionPropTheory.gas_stack_ok_def,
  vfmExecutionPropTheory.outputTo_consistent_stack_def,
  vfmExecutionPropTheory.outputTo_consistent_ctx_def,
  vfmExecutionPropTheory.wf_accounts_def,
  vfmExecutionPropTheory.wf_account_state_def]

Triviality linked_witness_deploy_typing:
  deploy_typing_ok_mods linked_witness_mods linked_witness_exports
    linked_witness_initial_machine linked_witness_deploy_tx
Proof
  rewrite_tac[deploy_typing_ok_mods_def, linked_check_deploy, linked_check_runtime] >>
  simp ([linked_witness_initial_machine_def, linked_witness_deploy_tx_def,
         p23_deploy_tx_def, vyperContextTheory.empty_call_txn_def,
         vyperInterpreterTheory.initial_machine_state_def, linked_deploy_length] @
        type_simps @ empty_accounts_simps) >>
  EVAL_TAC
QED

(* Use list membership to compute the declaration's position in each module. *)
Triviality linked_immutable_member:
  (?pre post vis ty.
      pre ++ [VariableDecl vis Immutable name ty (SOME off)] ++ post = tops /\
      width = type_mem_bytes fields ty) <=>
    ?vis ty. MEM (VariableDecl vis Immutable name ty (SOME off)) tops /\
             width = type_mem_bytes fields ty
Proof
  PURE_REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  EQ_TAC >> rw[]
  >- (qexistsl [`vis`, `ty`] >> simp[]) >>
  qpat_x_assum `MEM _ tops`
    (strip_assume_tac o REWRITE_RULE [listTheory.MEM_SPLIT]) >>
  qexistsl [`l1`, `l2`, `vis`, `ty`] >> simp[]
QED

(* The only immutable regions are the two annotated uint256 words. *)
Triviality linked_witness_immutable_regions:
  immutable_region_mods linked_witness_mods src name off width <=>
    name = "IMM" /\ width = 32 /\
    (src = NONE /\ off = 32 \/ src = SOME ^lib_id /\ off = 0)
Proof
  simp[bodyInvSplitTheory.immutable_region_mods_def, linked_witness_mods_def,
       alistTheory.ALOOKUP_def, linked_immutable_member, AllCaseEqs()] >>
  Cases_on `src` >> simp[] >> EVAL_TAC >>
  simp[GSYM CONJ_ASSOC, RIGHT_EXISTS_AND_THM] >>
  PURE_REWRITE_TAC [linked_immutable_member] >>
  EVAL_TAC >> simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED

val linked_immutable_length =
  (REWRITE_CONV [bodyInvSplitTheory.imm_len_mods_def] THENC EVAL)
    ``imm_len_mods linked_witness_mods``

(* The two word intervals partition the section, and the layouts are concrete. *)
Triviality linked_witness_layouts:
  layouts_agree_mods linked_witness_mods linked_witness_exports
    linked_witness_initial_machine linked_witness_deploy_tx
Proof
  simp[layouts_agree_mods_def, linked_witness_immutable_regions,
       linked_immutable_length, loweringStateRelDefsTheory.regions_disjoint_def,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >>
  rpt strip_tac >> gvs[linked_witness_mods_def] >> EVAL_TAC >> simp[] >>
  decide_tac
QED

Triviality linked_witness_deploy_state:
  deploy_state_rel_mods linked_witness_mods linked_witness_exports
    linked_witness_deploy_bc linked_witness_initial_machine
    linked_witness_deploy_tx linked_witness_es_deploy
Proof
  rewrite_tac[deploy_state_rel_mods_def, linked_witness_layouts] >>
  qexistsl [`p23_frame linked_witness_deploy_bc [] (Code 2w)`,
            `p23_dep_rollback`, `[]`] >>
  rewrite_tac[linked_ctor_encoding, linked_deploy_env] >>
  simp ([linked_witness_es_deploy_def, p23_es_dep_def,
         p23_frame_def, p23_dep_rollback_def, linked_witness_initial_machine_def,
         linked_witness_deploy_tx_def, p23_deploy_tx_def,
         vyperContextTheory.empty_call_txn_def,
         vyperInterpreterTheory.initial_machine_state_def,
         vfmStateTheory.account_empty_def, e2eDefsTheory.value_transfer_ok_def,
         e2eDefsTheory.accounts_after_transfer_def, linked_witness_mods_def,
         vfmTotalBalanceTheory.balance_bounded_def,
         vfmTotalBalanceTheory.total_balance_def, pred_setTheory.SUM_IMAGE_ZERO] @
        frame_wf_simps @ empty_accounts_simps) >>
  `SUM_IMAGE (\x : address. 0) UNIV = 0` by
    simp[pred_setTheory.SUM_IMAGE_ZERO] >>
  simp[vyperInterpreterTheory.bind_arguments_def, listTheory.REV_DEF,
       e2eDefsTheory.tx_block_fields_rel_def, p23_tx_params_def,
       loweringStateRelDefsTheory.tx_env_ok_def]
QED

Theorem linked_witness_deploy_premises:
  asm_opt_finalizer IN accepted_finalizers /\
  compile_vyper_mods asm_opt_finalizer (o1_policy all_capabilities)
    linked_witness_mods linked_witness_exports =
    SOME (linked_witness_deploy_bc, linked_witness_runtime_bc) /\
  deploy_typing_ok_mods linked_witness_mods linked_witness_exports
    linked_witness_initial_machine linked_witness_deploy_tx /\
  deploy_state_rel_mods linked_witness_mods linked_witness_exports
    linked_witness_deploy_bc linked_witness_initial_machine
    linked_witness_deploy_tx linked_witness_es_deploy /\
  LENGTH (call_trace linked_witness_es_deploy) < 2 ** 64
Proof
  simp[accepted_finalizers_def, linked_witness_compile, linked_witness_deploy_typing,
       linked_witness_deploy_state, linked_deploy_trace]
QED

(* Keep the checked EVM post-state in its cv representation for later runs. *)
val linked_deploy_run = cv_eval_pat
  (cvSome (cvTuple [cvEval EVAL, cvName "linked_witness_es_deploy_post"]))
  ``run_call linked_witness_es_deploy``

Triviality linked_witness_deploy_run:
  run_call linked_witness_es_deploy = SOME (INR NONE, linked_witness_es_deploy_post)
Proof
  ACCEPT_TAC linked_deploy_run
QED

Definition linked_witness_am_deploy_post_def:
  linked_witness_am_deploy_post =
    case load_contract (SOME []) [] linked_witness_initial_machine
           linked_witness_deploy_tx linked_witness_mods linked_witness_exports of
    | INL (am, _) => am
    | INR _ => linked_witness_initial_machine
End

Definition linked_witness_am_call_def:
  linked_witness_am_call =
    next_source_machine linked_witness_am_deploy_post
      (SND (THE (run_call linked_witness_es_deploy)))
End

Definition linked_witness_installed_code_def:
  linked_witness_installed_code =
    linked_witness_runtime_bc ++ word_to_bytes (5w : bytes32) T ++
    word_to_bytes (7w : bytes32) T
End

Definition linked_witness_deployed_accounts_def:
  linked_witness_deployed_accounts = update_account 2w
    (empty_account_state with
      <| code := linked_witness_installed_code;
         storage := update_storage 1w 2w (update_storage 0w 1w empty_storage) |>)
    empty_accounts
End

val () = cv_auto_trans linked_witness_installed_code_def
val () = cv_auto_trans linked_witness_deployed_accounts_def

val linked_committed_accounts = EQT_ELIM (cv_eval
  ``process_deletions linked_witness_es_deploy_post.rollback.toDelete
      linked_witness_es_deploy_post.rollback.accounts =
    linked_witness_deployed_accounts``)

val linked_call_machine = SIMP_CONV (srw_ss())
  [linked_witness_am_call_def, linked_witness_deploy_run,
   e2eDefsTheory.next_source_machine_def, linked_committed_accounts]
  ``linked_witness_am_call``

val linked_call_selector = cv_eval ``function_selector "locked_get_x" []``

Definition linked_witness_calldata_def:
  linked_witness_calldata : word8 list = ^(rhs (concl linked_call_selector))
End

Definition linked_witness_call_tx_def:
  linked_witness_call_tx = p23_call_tx with
    <| function_name := "locked_get_x"; calldata := linked_witness_calldata;
       code := linked_witness_installed_code |>
End

Definition linked_witness_es_call_def:
  linked_witness_es_call =
    let es = p23_es_call_of linked_witness_es_deploy_post in
      es with contexts :=
        [(p23_frame (lookup_account 2w es.rollback.accounts).code
           linked_witness_calldata (Memory <| offset := 0; size := 0 |>),
          es.rollback)]
End

val () = cv_auto_trans linked_witness_calldata_def
val () = cv_auto_trans linked_witness_es_call_def

val linked_call_trace = MATCH_MP frame_quiet_obs (EQT_ELIM (cv_eval
  ``frame_quiet_tr (LENGTH linked_witness_es_call.contexts)
     linked_witness_es_call (step linked_witness_es_call)``))

val linked_source_deploy = EVAL
  ``load_contract (SOME []) [] linked_witness_initial_machine
    linked_witness_deploy_tx linked_witness_mods linked_witness_exports``
val _ = sumSyntax.dest_inl (rhs (concl linked_source_deploy))

val linked_source_machine = SIMP_CONV (srw_ss())
  [linked_witness_am_deploy_post_def, linked_source_deploy]
  ``linked_witness_am_deploy_post``

val linked_call_layout = TRANS
  ((REWRITE_CONV [linked_call_machine, linked_source_machine] THENC EVAL)
    ``linked_witness_am_call.layouts``)
  (SYM (EVAL ``linked_witness_initial_machine.layouts``))

val linked_call_target = EVAL ``linked_witness_call_tx.target``
val linked_deploy_target = EVAL ``linked_witness_deploy_tx.target``
val linked_targets_agree = TRANS linked_call_target (SYM linked_deploy_target)

val linked_call_immutables =
  (REWRITE_CONV [linked_call_machine, linked_source_machine] THENC EVAL)
    ``account_immutables linked_witness_am_call linked_witness_call_tx.target``

val linked_run_art = optionSyntax.dest_some (rhs (concl linked_check_runtime))

(* The runtime checker and deployed machine give finite maps on concrete keys. *)
Triviality linked_witness_global_cells:
  global_cells_typed_mods linked_witness_mods (^linked_run_art).cta_bare_globals
    (account_immutables linked_witness_am_call linked_witness_call_tx.target)
Proof
  simp[global_cells_typed_mods_def, linked_call_immutables] >>
  rpt gen_tac >> EVAL_TAC >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]
QED

(* Evaluate the exports and all three namespace tests on the linked AST. *)
Triviality linked_witness_export_names:
  exports_ok linked_witness_am_call.layouts linked_witness_call_tx.target
    linked_witness_mods linked_witness_exports /\
  EVERY (\(name, src).
    MEM (SOME src, name)
      (contract_keys external_name_keys_toplevel linked_witness_mods))
    linked_witness_exports /\
  ALL_DISTINCT (MAP FST linked_witness_exports) /\
  EVERY (\(name, _).
    ~MEM (NONE, name)
      (contract_keys self_member_keys_toplevel linked_witness_mods))
    linked_witness_exports
Proof
  PURE_REWRITE_TAC [linked_call_layout, linked_targets_agree] >> EVAL_TAC
QED

Triviality linked_witness_source_typing:
  source_typing_ok_mods linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx
Proof
  rewrite_tac[source_typing_ok_mods_def, linked_witness_export_names] >>
  simp[linked_call_layout, linked_targets_agree, linked_check_runtime,
       REWRITE_RULE [linked_targets_agree] linked_witness_global_cells] >>
  rewrite_tac[linked_call_machine, linked_source_machine] >>
  simp ([linked_witness_am_deploy_post_def, linked_call_immutables,
         linked_witness_call_tx_def, p23_call_tx_def,
         vyperContextTheory.empty_call_txn_def, linked_witness_mods_def,
         linked_witness_deployed_accounts_def, vfmStateTheory.update_account_def,
         combinTheory.APPLY_UPDATE_THM] @ type_simps @ empty_accounts_simps) >>
  rpt conj_tac >> rpt gen_tac >> EVAL_TAC >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[] >>
  Cases_on `addr = 2w` >> gvs[] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >> simp[]
QED

val linked_witness_section =
  ``word_to_bytes (5w : bytes32) T ++ word_to_bytes (7w : bytes32) T``

val linked_immutable_simps = [
  immutableEncodingTheory.immutable_value_admissible_def,
  immutableEncodingTheory.encode_immutable_value_def,
  immutableEncodingTheory.immutable_word_bytes_def,
  immutableEncodingTheory.immutable_fit_def,
  immutableValueTheory.immutable_value_mask_def,
  immutableValueTheory.immutable_mask_fit_def,
  valueEncodingDefsTheory.val_in_memory_def,
  valueEncodingDefsTheory.mem_word_at_def,
  valueEncodingTheory.type_memory_size_def,
  valueEncodingTheory.typed_val_to_w256_def,
  valueEncodingTheory.val_to_w256_def]

(* Read back the constructor's two immutable values in allocated offset order. *)
Triviality linked_witness_immutable_section:
  immutables_section_rel_mods linked_witness_mods
    (account_immutables linked_witness_am_call linked_witness_call_tx.target)
    ^linked_witness_section
Proof
  simp[immutables_section_rel_mods_def, linked_immutable_length,
       linked_witness_immutable_regions, linked_call_immutables] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp linked_immutable_simps >> EVAL_TAC >> simp[]
QED

(* The balances are all zero, including the newly installed contract. *)
Triviality linked_witness_deployed_balance:
  total_balance linked_witness_deployed_accounts = 0
Proof
  simp[vfmTotalBalanceTheory.total_balance_def, pred_setTheory.SUM_IMAGE_ZERO] >>
  qx_gen_tac `addr` >> Cases_on `2w = addr` >>
  simp ([linked_witness_deployed_accounts_def, vfmStateTheory.update_account_def,
         combinTheory.APPLY_UPDATE_THM] @ empty_accounts_simps)
QED

(* The actual post-deploy source machine retains the checked layout and lock. *)
Triviality linked_witness_call_deployment:
  source_deployment_rel_mods linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx
Proof
  rewrite_tac[source_deployment_rel_mods_def] >>
  `layouts_agree_mods linked_witness_mods linked_witness_exports
     linked_witness_am_call linked_witness_call_tx` by
    (mp_tac linked_witness_layouts >>
     PURE_REWRITE_TAC [layouts_agree_mods_def, linked_call_layout,
                       linked_targets_agree] >> simp[]) >>
  simp[] >>
  rewrite_tac[linked_call_machine, linked_source_machine] >> EVAL_TAC
QED

Triviality linked_witness_installed:
  installed_code_rel_mods linked_witness_mods linked_witness_runtime_bc
    (account_immutables linked_witness_am_call linked_witness_call_tx.target)
    linked_witness_installed_code
Proof
  rewrite_tac[installed_code_rel_mods_def, linked_witness_installed_code_def] >>
  qexists_tac `^linked_witness_section` >>
  simp[linked_witness_immutable_section]
QED

Triviality linked_witness_call_state:
  call_state_rel_mods linked_witness_mods linked_witness_exports
    linked_witness_runtime_bc linked_witness_am_call linked_witness_call_tx
    linked_witness_es_call
Proof
  rewrite_tac[call_state_rel_mods_def, linked_witness_call_deployment,
              e2eDefsTheory.evm_state_ok_def, e2eDefsTheory.frame_fresh_def,
              e2eDefsTheory.frame_tx_rel_def, e2eDefsTheory.world_rel_def,
              linked_call_immutables] >>
  simp[linked_witness_es_call_def, p23_es_call_of_def, linked_committed_accounts,
       p23_frame_def, linked_witness_call_tx_def, p23_call_tx_def,
       vyperContextTheory.empty_call_txn_def, linked_witness_calldata_def,
       vfmStateTheory.account_empty_def, linked_call_machine, linked_source_machine,
       e2eDefsTheory.value_transfer_ok_def, e2eDefsTheory.accounts_after_transfer_def,
       e2eDefsTheory.tx_block_fields_rel_def, p23_tx_params_def,
       loweringStateRelDefsTheory.tx_env_ok_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmTotalBalanceTheory.balance_bounded_def, linked_witness_deployed_balance,
       vfmReturndataBoundTheory.returndata_bounded_def,
       vfmCalldataBoundTheory.calldata_bounded_def,
       vfmCalldataBoundTheory.memory_paid_def, vfmCalldataBoundTheory.frames_paid_def,
       vfmCalldataBoundTheory.outputs_fit_def] >>
  simp (frame_wf_simps @ empty_accounts_simps @
        [linked_witness_deployed_accounts_def, vfmStateTheory.update_account_def,
         combinTheory.APPLY_UPDATE_THM,
         REWRITE_RULE [linked_call_immutables] linked_witness_installed]) >>
  rpt conj_tac >> rpt gen_tac >> EVAL_TAC >> simp[]
  >- (Cases_on `x = 2w` >> simp[])
QED

val linked_horizon =
  ``([(F, 0w : bytes32, BaseTV (UintT 256))], [context$global_nonreentrant_slot])``

Triviality linked_witness_storage:
  e2eCorrectness$storage_ok ^linked_horizon linked_witness_am_call linked_witness_call_tx
Proof
  rewrite_tac[e2eCorrectnessTheory.storage_ok_def, linked_call_machine,
              linked_source_machine] >>
  simp[vyperStorageFootprintTheory.regions_consistent_def,
       vyperStorageFootprintTheory.storage_locks_separated_def,
       vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  EVAL_TAC >> simp[]
QED

val linked_dispatch = EQT_ELIM (EVAL
  ``calldata_dispatch_mods linked_witness_mods linked_witness_exports
      linked_witness_call_tx.calldata = SOME ("locked_get_x", [])``)

val linked_storage_trace =
  (REWRITE_CONV [linked_call_machine, linked_source_machine] THENC EVAL)
    ``source_storage_trace linked_witness_am_call
        (linked_witness_call_tx with <| function_name := "locked_get_x"; args := [] |>)
        [] gobs``

(* Verify the selected call actually observes the shared lock. *)
val _ = EQT_ELIM ((REWRITE_CONV [linked_storage_trace] THENC EVAL)
  ``MEM (StorageLock context$global_nonreentrant_slot)
      (source_storage_trace linked_witness_am_call
        (linked_witness_call_tx with <| function_name := "locked_get_x"; args := [] |>)
        [] gobs)``)

(* The selected imported function observes the lock and its own storage slot. *)
Triviality linked_witness_call_within:
  call_within_mods ^linked_horizon linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx linked_witness_es_call
Proof
  simp[call_within_mods_def, linked_dispatch, linked_call_trace] >>
  gen_tac >> rewrite_tac[linked_storage_trace, linked_call_machine, linked_source_machine] >>
  EVAL_TAC >> simp[]
QED

Theorem linked_witness_call_premises:
  asm_opt_finalizer IN accepted_finalizers /\
  compile_vyper_mods asm_opt_finalizer (o1_policy all_capabilities)
    linked_witness_mods linked_witness_exports =
    SOME (linked_witness_deploy_bc, linked_witness_runtime_bc) /\
  source_typing_ok_mods linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx /\
  call_state_rel_mods linked_witness_mods linked_witness_exports
    linked_witness_runtime_bc linked_witness_am_call linked_witness_call_tx
    linked_witness_es_call /\
  LENGTH (call_trace linked_witness_es_call) < 2 ** 64 /\
  e2eCorrectness$storage_ok ^linked_horizon linked_witness_am_call linked_witness_call_tx /\
  call_within_mods ^linked_horizon linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx linked_witness_es_call
Proof
  simp[accepted_finalizers_def, linked_witness_compile, linked_witness_source_typing,
       linked_witness_call_state, linked_call_trace, linked_witness_storage,
       linked_witness_call_within]
QED

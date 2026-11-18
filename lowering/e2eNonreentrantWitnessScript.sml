Theory e2eNonreentrantWitness
Ancestors
  e2eWitnessCompute e2eDefs e2eDeployDefs
  supportedProgram immutableSectionRel alist integer_word option
  compileVyper e2eProducers vfmRunCall callTrace
  vyperCalldata vyperInterpreter
Libs
  finite_mapLib computeLib wordsLib intReduce cv_transLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

(* This fixture uses ordinary function declarations for both getters.
   Both getters meet the call correctness and outer gas-sufficiency premises
   after the same optimized deployment. The ordinary getter also satisfies
   valid_vyper_call. The trace and storage facts here hold at the fixture's
   gas limits. The gas theorems' guards at arbitrary added gas need a
   separate proof. *)
local
  val tops = ``
    [FunctionDecl External Nonpayable F F "get" [] [] (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 42)))];
     FunctionDecl External Nonpayable T F "locked_get" [] [] (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 43)))]]``

  val () = computeLib.add_funs (map cv_eval [
    ``vyperABIEntries$abi_method_id FEMPTY "get" []``,
    ``vyperABIEntries$abi_method_id FEMPTY "locked_get" []``,
    ``function_selector "get" []``,
    ``function_selector "locked_get" []``])
  val normalize_bytes =
    PURE_ONCE_REWRITE_CONV [GSYM wordsTheory.n2w_mod] THENC
    DEPTH_CONV wordsLib.SIZES_CONV THENC numLib.REDUCE_CONV
  val compile = CONV_RULE (RAND_CONV normalize_bytes) (EVAL ``
    compile_vyper asm_opt_finalizer (o1_policy all_capabilities) ^tops``)
  val (deploy_bc, runtime_bc) =
    pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl compile)))
  val am_dep = ``initial_machine_state with
    layouts := [(2w, ([], [((NONE, "$.nonreentrant_key"),
                           context$global_nonreentrant_slot)]))]``
  val tx_dep = ``p23_deploy_tx with code := ^deploy_bc``
  val es_dep = ``
    <| contexts := [(p23_frame ^deploy_bc [] (Code 2w), p23_dep_rollback)];
       txParams := p23_tx_params; rollback := p23_dep_rollback;
       originalAccounts := empty_accounts; msdomain := Collect empty_domain |>``
  val dep_run = cv_eval ``run_call ^es_dep``
  fun run_post th =
    snd (pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl th))))
  val es_dep_post = run_post dep_run
  val load = EVAL ``load_contract (SOME []) [] ^am_dep ^tx_dep [(NONE,^tops)] []``
  val (am_dep_post, _) = pairSyntax.dest_pair (fst (sumSyntax.dest_inl (rhs (concl load))))
  val am_call = ``next_source_machine ^am_dep_post ^es_dep_post``
  val call_tx = ``\name data. p23_call_tx with
    <| function_name := name; calldata := data; code := ^runtime_bc |>``
  val get_data_eval = EVAL ``p23_get_calldata``
  val get_data = rhs (concl get_data_eval)
  val get_calldata_encodes = TRANS (SYM get_data_eval) p23_get_calldata_encodes
  val locked_data = rhs (concl (EVAL ``function_selector "locked_get" []``))
  val get_tx = rhs (concl (DEPTH_CONV BETA_CONV ``^call_tx "get" ^get_data``))
  val locked_tx =
    rhs (concl (DEPTH_CONV BETA_CONV ``^call_tx "locked_get" ^locked_data``))
  val call_world = ``process_deletions (^es_dep_post).rollback.toDelete
    (^es_dep_post).rollback.accounts``
  val call_accounts = ``update_account 2w
    (empty_account_state with code := ^runtime_bc)
    empty_accounts``
  val call_world_eval = EVAL call_world
  val call_rollback = ``p23_dep_rollback with accounts := ^call_accounts``
  val call_es = ``\data.
    <| contexts := [(p23_frame ^runtime_bc data
                      (Memory <| offset := 0; size := 0 |>), ^call_rollback)];
       txParams := p23_tx_params; rollback := ^call_rollback;
       originalAccounts := ^call_accounts; msdomain := Collect empty_domain |>``
  fun call_frame data =
    rhs (concl (BETA_CONV ``^call_es ^data``))
  val get_es = call_frame get_data
  val locked_es = call_frame locked_data
  val get_run = cv_eval ``run_call ^get_es``
  val locked_run = cv_eval ``run_call ^locked_es``
  val get_post = run_post get_run
  val locked_post = run_post locked_run
  fun quiet es =
    MATCH_MP frame_quiet_obs (EQT_ELIM (cv_eval
      ``frame_quiet_tr (LENGTH (^es).contexts) ^es (step ^es)``))
  val dep_trace = quiet es_dep
  val get_trace = quiet get_es
  val locked_trace = quiet locked_es
  val am_call_eval = EVAL am_call
  val dep_tx_eval = EVAL tx_dep
  val check_dep = EVAL ``check_contract T (^am_dep).layouts 2w [(NONE,^tops)]``
  val check_run = EVAL ``check_contract F (^am_dep).layouts 2w [(NONE,^tops)]``
  val compile_guards = map EVAL [
    ``program_reads_self_code ^tops``,
    ``supported_program ^tops``,
    ``supported_program_deploy ^tops``,
    ``~(?t. ^runtime_bc = 0xEFw :: t)``]
  val ctor_free = SIMP_RULE (srw_ss())
    [supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
     supportedStmtTraverseTheory.supported_assignment_exists_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     constructor_call_root_def] (EVAL ``constructor_call_free ^tops``)
  val ctor_encoding = EVAL ``constructor_args_encode ^tops ^tx_dep []``
  val dep_env = EVAL ``tx_block_fields_rel ^tx_dep p23_tx_params``

  val deploy_witnesses = [``p23_frame ^deploy_bc [] (Code 2w)``,
                          ``p23_dep_rollback``, ``[] : word8 list``]
  val account_simps = [
    vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
    vfmStateTheory.empty_account_state_def, combinTheory.APPLY_UPDATE_THM]
  val frame_wf = [
    vfmExecutionPropTheory.wf_state_def, vfmExecutionPropTheory.wf_context_def,
    vfmExecutionPropTheory.all_accounts_def,
    vfmExecutionPropTheory.stack_room_ok_def, vfmExecutionPropTheory.gas_stack_ok_def,
    vfmExecutionPropTheory.outputTo_consistent_stack_def,
    vfmExecutionPropTheory.outputTo_consistent_ctx_def,
    vfmReturndataBoundTheory.returndata_bounded_def]
  val tx_wt = vyperTypeContractSoundnessTheory.call_tx_well_typed_def
  val machine_wt = [
    vyperTypeInitialStateTheory.machine_well_typed_def,
    vyperTypeInvariantsTheory.accounts_well_typed_def,
    vyperTypeInvariantsTheory.account_well_typed_def,
    vyperTypeInvariantsTheory.imms_well_typed_def]
  val empty_tx = vyperContextTheory.empty_call_txn_def
  val init_am = vyperInterpreterTheory.initial_machine_state_def

Triviality optimized_getters_deploy_typing:
  deploy_typing_ok ^tops ^am_dep ^tx_dep
Proof
  simp ([deploy_typing_ok_def, init_am, p23_deploy_tx_def, empty_tx,
         tx_wt, SIMP_RULE (srw_ss()) [init_am] check_dep,
         SIMP_RULE (srw_ss()) [init_am] check_run] @ machine_wt @ account_simps)
QED

Triviality optimized_getters_deploy_state:
  deploy_state_rel ^tops ^deploy_bc ^am_dep ^tx_dep ^es_dep
Proof
  rewrite_tac[deploy_state_rel_def] >>
  MAP_EVERY exists_tac deploy_witnesses >>
  rewrite_tac[ctor_encoding, dep_env, dep_tx_eval] >>
  simp ([p23_frame_def, p23_dep_rollback_def,
         layouts_agree_def, init_am, vfmStateTheory.account_empty_def,
         value_transfer_ok_def, accounts_after_transfer_def,
         vfmTotalBalanceTheory.balance_bounded_def, vfmTotalBalanceTheory.total_balance_def,
         vfmExecutionPropTheory.wf_accounts_def,
         vfmExecutionPropTheory.wf_account_state_def] @
        frame_wf @ account_simps) >>
  simp [vfmTotalBalanceTheory.total_balance_def, pred_setTheory.SUM_IMAGE_ZERO,
        vyperInterpreterTheory.bind_arguments_def, listTheory.REV_DEF,
        tx_block_fields_rel_def, p23_tx_params_def,
        loweringStateRelDefsTheory.tx_env_ok_def] >>
  `SUM_IMAGE (\x : address. 0) UNIV = 0` by
    simp[pred_setTheory.SUM_IMAGE_ZERO] >>
  simp[]
QED

Triviality optimized_getters_source_typing:
  !name data. LENGTH data < 2 ** 256 ==>
    source_typing_ok ^tops ^am_call (^call_tx name data)
Proof
  rpt strip_tac >>
  gvs ([source_typing_ok_def, am_call_eval, p23_call_tx_def, empty_tx,
        SIMP_RULE (srw_ss())
          [init_am, contextTheory.global_nonreentrant_slot_def] check_run, tx_wt,
         global_cells_typed_def, account_immutables_def,
         vyperTypeContractTheory.constants_fold_module_def] @ machine_wt) >>
  rpt gen_tac >> Cases_on `addr = 2w` >> simp account_simps
QED

Triviality optimized_getters_accounts:
  ^call_world = ^call_accounts
Proof
  PURE_REWRITE_TAC [call_world_eval] >>
  simp [FUN_EQ_THM, vfmStateTheory.update_account_def] >>
  qx_gen_tac `address` >> Cases_on `address = 2w` >>
  simp (account_simps @ [vfmStateTheory.account_state_component_equality,
                         vfmStateTheory.empty_storage_def, combinTheory.K_DEF,
                         FUN_EQ_THM])
QED

Triviality optimized_getters_balance:
  vfmTotalBalance$total_balance ^call_accounts = 0
Proof
  simp[vfmTotalBalanceTheory.total_balance_def, pred_setTheory.SUM_IMAGE_ZERO,
       vfmStateTheory.update_account_def] >>
  qx_gen_tac `address` >> Cases_on `address = 2w` >> simp account_simps
QED

Triviality optimized_getters_accounts_wf:
  vfmExecutionProp$wf_accounts ^call_accounts
Proof
  simp[vfmExecutionPropTheory.wf_accounts_def,
       vfmStateTheory.update_account_def] >>
  qx_gen_tac `address` >> Cases_on `address = 2w` >>
  simp (vfmExecutionPropTheory.wf_account_state_def :: account_simps)
QED

Triviality optimized_getters_call_state:
  !name data. LENGTH data < 2 ** 64 ==>
    call_state_rel ^tops ^runtime_bc ^am_call (^call_tx name data) (^call_es data)
Proof
  rpt strip_tac >>
  assume_tac optimized_getters_accounts_wf >>
  assume_tac optimized_getters_balance >>
  rewrite_tac[call_state_rel_def, evm_state_ok_def, frame_fresh_def,
              frame_tx_rel_def, world_rel_def, next_source_machine_def,
              optimized_getters_accounts] >>
  simp ([am_call_eval, p23_frame_def, p23_dep_rollback_def, p23_call_tx_def,
         empty_tx, p23_tx_params_def, LET_THM, vfmStateTheory.account_empty_def,
         value_transfer_ok_def, accounts_after_transfer_def,
         tx_block_fields_rel_def, loweringStateRelDefsTheory.tx_env_ok_def,
         vfmCalldataBoundTheory.calldata_bounded_def,
         vfmCalldataBoundTheory.memory_paid_def, vfmCalldataBoundTheory.frames_paid_def,
         vfmCalldataBoundTheory.outputs_fit_def, source_deployment_rel_def,
         layouts_agree_def, vfmTotalBalanceTheory.balance_bounded_def,
         optimized_getters_balance, optimized_getters_accounts_wf,
         vfmStateTheory.update_account_def,
         immutableSectionRelTheory.installed_code_rel_def] @
        frame_wf @ account_simps) >>
  simp[immutableSectionRelTheory.immutables_section_rel_def,
       compileVyperTheory.compute_immutables_len_def, listTheory.APPEND_EQ_CONS] >>
  gvs (contextTheory.global_nonreentrant_slot_def ::
       vfmStateTheory.update_account_def :: account_simps)
QED

  fun instantiate_call name data th =
    let
      val instance = BETA_RULE (SPECL [name, data] th)
      val (bound, _) = dest_imp (concl instance)
    in
      MP instance (EQT_ELIM (EVAL bound))
    end
  val get_facts = map (instantiate_call ``"get"`` get_data)
    [optimized_getters_source_typing, optimized_getters_call_state]
  val locked_facts = map (instantiate_call ``"locked_get"`` locked_data)
    [optimized_getters_source_typing, optimized_getters_call_state]
  val get_lookup = EVAL
    ``vyperInterpreter$lookup_function NONE "get" External ^tops``

Triviality optimized_getter_valid:
  e2eDefs$valid_vyper_call ^tops ^get_tx
    (buffer_to_list (FST (HD (^get_es).contexts)).msgParams.data) (BaseT (UintT 256))
Proof
  simp[p23_frame_def, e2eDefsTheory.valid_vyper_call_def, p23_call_tx_def,
       empty_tx, get_lookup, vyperInterpreterTheory.bind_arguments_def,
       selectorDispatchTheory.calldata_encodes_def, get_calldata_encodes]
QED

  val witnesses = [
    ``o1_policy all_capabilities``, tops, deploy_bc, runtime_bc, am_dep,
    tx_dep, es_dep, es_dep_post, am_dep_post, get_tx, get_es, get_post,
    locked_tx, locked_es, locked_post]
  val call_facts = map EVAL [
    ``calldata_dispatch ^tops (^get_tx).calldata =
      SOME ((^get_tx).function_name, (^get_tx).args)``,
    ``calldata_dispatch ^tops (^locked_tx).calldata =
      SOME ((^locked_tx).function_name, (^locked_tx).args)``,
    ``vyperInterpreter$lookup_function NONE (^locked_tx).function_name External ^tops``,
    ``FST (call_external (SOME []) [] ^am_call ^get_tx) = INL (IntV 42)``,
    ``FST (call_external (SOME []) [] ^am_call ^locked_tx) = INL (IntV 43)``,
    ``(FST (HD (^get_post).contexts)).returnData = word_to_bytes (42w : bytes32) T``,
    ``(FST (HD (^locked_post).contexts)).returnData = word_to_bytes (43w : bytes32) T``]
  val storage_guards = map (REWRITE_RULE [] o EVAL) [
    ``deploy_storage_ok ^tops ^am_dep ^tx_dep [] []``,
    ``call_storage_ok ^am_call ^get_tx [] []``,
    ``call_storage_ok ^am_call ^locked_tx [] []``]
in

Theorem asm_opt_nonreentrant_deploy_and_call_premises_jointly_satisfiable:
  ?policy tops deploy_bc runtime_bc am_dep tx_dep es_dep es_dep'
     am_dep' tx_get es_get es_get' tx_locked es_locked es_locked'.
    asm_opt_finalizer IN accepted_finalizers /\
    ~program_reads_self_code tops /\
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc,runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\ ~(?t. runtime_bc = 0xEFw :: t) /\
    deploy_typing_ok tops am_dep tx_dep /\
    deploy_state_rel tops deploy_bc am_dep tx_dep es_dep /\
    run_call es_dep = SOME (INR NONE,es_dep') /\
    call_trace es_dep = [] /\ gas_readings es_dep = [] /\
    deploy_storage_ok tops am_dep tx_dep [] [] /\
    load_contract (SOME []) [] am_dep tx_dep [(NONE,tops)] [] = INL (am_dep',[]) /\
    source_typing_ok tops (next_source_machine am_dep' es_dep') tx_get /\
    call_state_rel tops runtime_bc (next_source_machine am_dep' es_dep') tx_get es_get /\
    e2eDefs$valid_vyper_call tops tx_get
      (buffer_to_list (FST (HD es_get.contexts)).msgParams.data) (BaseT (UintT 256)) /\
    calldata_dispatch tops tx_get.calldata =
      SOME (tx_get.function_name,tx_get.args) /\
    call_trace es_get = [] /\ gas_readings es_get = [] /\
    call_storage_ok (next_source_machine am_dep' es_dep') tx_get [] [] /\
    run_call es_get = SOME (INR NONE,es_get') /\
    FST (call_external (SOME []) [] (next_source_machine am_dep' es_dep') tx_get) =
      INL (IntV 42) /\
    (FST (HD es_get'.contexts)).returnData = word_to_bytes (42w : bytes32) T /\
    source_typing_ok tops (next_source_machine am_dep' es_dep') tx_locked /\
    call_state_rel tops runtime_bc (next_source_machine am_dep' es_dep') tx_locked es_locked /\
    calldata_dispatch tops tx_locked.calldata =
      SOME (tx_locked.function_name,tx_locked.args) /\
    (?mut args dflts ret body.
      vyperInterpreter$lookup_function NONE tx_locked.function_name External tops =
        SOME (mut,T,args,dflts,ret,body)) /\
    call_trace es_locked = [] /\ gas_readings es_locked = [] /\
    call_storage_ok (next_source_machine am_dep' es_dep') tx_locked [] [] /\
    run_call es_locked = SOME (INR NONE,es_locked') /\
    FST (call_external (SOME []) [] (next_source_machine am_dep' es_dep') tx_locked) =
      INL (IntV 43) /\
    (FST (HD es_locked'.contexts)).returnData = word_to_bytes (43w : bytes32) T
Proof
  MAP_EVERY exists_tac witnesses >>
  rewrite_tac ([compile,
         ctor_free, optimized_getters_deploy_typing, optimized_getters_deploy_state,
         dep_run, dep_trace, load, get_trace, get_run, optimized_getter_valid,
         locked_trace, locked_run] @
        compile_guards @ get_facts @ locked_facts @ call_facts @ storage_guards) >>
  simp[asmOptimizerTheory.accepted_finalizers_def]
QED

end

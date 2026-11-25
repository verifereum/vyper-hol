Theory e2eNonreentrantWitness
Ancestors
  e2eWitnessCompute e2eDefs e2eDeployDefs e2eCorrectness
  e2eDeployed
  immutableSectionRel alist integer_word option vyperStorageFootprint
  compileVyper e2eProducers vfmRunCall callTrace
  vyperCalldata vyperInterpreter
  e2eGasSufficient e2eGasSufficientTop[qualified,ignore_grammar]
  frameGas callTraceEntryProvenance callTraceRootMetadata
Libs
  finite_mapLib computeLib wordsLib intReduce cv_transLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

(* This fixture uses ordinary function declarations for both getters.
   Both getters meet the call correctness and outer gas-sufficiency premises
   after the same optimized deployment. The ordinary getter also satisfies
   valid_vyper_call. The storage horizons cover every source gas filling.
   The call gas theorem's guards at arbitrary added frame gas need a
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
  rpt gen_tac >> Cases_on `addr = 2w` >>
  simp (vfmExecutionTheory.process_deletions_def :: account_simps)
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

  val get_horizon = ``([] : (bool # bytes32 # type_value) list, [] : num list)``
  val locked_horizon =
    ``([] : (bool # bytes32 # type_value) list, [context$global_nonreentrant_slot])``

  fun trace_bound es trace =
    prove (``LENGTH (call_trace ^es) < 2 ** 64``, simp[trace])

  fun call_storage_facts (horizon, tx, es, trace) =
    let
      val dispatch = EVAL ``calldata_dispatch ^tops (^tx).calldata``
      val storage = prove (``storage_ok ^horizon ^am_call ^tx``,
        simp[storage_ok_def, regions_consistent_def, storage_locks_separated_def,
             storage_well_formed_on_def])
      val within = prove (``call_within ^horizon ^tops ^am_call ^tx ^es``,
        simp[call_within_def, dispatch, trace] >> gen_tac >> EVAL_TAC)
    in
      [trace_bound es trace, storage, within]
    end

  val get_storage =
    call_storage_facts (get_horizon, get_tx, get_es, get_trace)
  val locked_storage =
    call_storage_facts (locked_horizon, locked_tx, locked_es, locked_trace)
  val dep_bound = trace_bound es_dep dep_trace

  val accepted = prove (``asm_opt_finalizer IN accepted_finalizers``,
    simp[asmOptimizerTheory.accepted_finalizers_def])
  val compiler_args =
    [``asm_opt_finalizer``, ``o1_policy all_capabilities``, tops, deploy_bc, runtime_bc]
  val common_premises = [accepted, compile]
  val deploy_args = compiler_args @ [am_dep, tx_dep, es_dep]
  val deploy_premises =
    common_premises @ [optimized_getters_deploy_typing, optimized_getters_deploy_state]

  val _ = MATCH_MP
    (SPECL deploy_args e2e_deploy_correctness_deployed)
    (LIST_CONJ (deploy_premises @ [dep_bound]))
  val _ = MATCH_MP
    (SPECL deploy_args e2eGasSufficientTopTheory.e2e_deploy_gas_sufficient)
    (LIST_CONJ deploy_premises)

  fun check_call (horizon, tx, es, entry_facts, storage_facts) =
    let
      val args = compiler_args @ [am_call, tx, es]
      val call_premises = CONJUNCTS (REWRITE_RULE [call_premises_deployed]
        (LIST_CONJ entry_facts))
      val premises = common_premises @ call_premises
      val _ = MATCH_MP (SPECL (args @ [horizon]) vyper_call_correct_deployed)
        (LIST_CONJ (premises @ storage_facts))
      val _ = MATCH_MP
        (SPECL args vyper_call_gas_sufficient_deployed)
        (LIST_CONJ premises)
    in
      ()
    end
  val () = check_call (get_horizon, get_tx, get_es, get_facts, get_storage)
  val () = check_call (locked_horizon, locked_tx, locked_es, locked_facts, locked_storage)

  val witnesses = [
    ``o1_policy all_capabilities``, tops, deploy_bc, runtime_bc, am_dep,
    tx_dep, es_dep, es_dep_post, am_dep_post, get_tx, get_es, get_post,
    locked_tx, locked_es, locked_post, get_horizon, locked_horizon]
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
  val deploy_guard = REWRITE_RULE [] (EVAL
    ``deploy_storage_ok ^tops ^am_dep ^tx_dep [] []``)
in

Theorem asm_opt_nonreentrant_deploy_and_call_premises_jointly_satisfiable:
  ?policy tops deploy_bc runtime_bc am_dep tx_dep es_dep es_dep'
     am_dep' tx_get es_get es_get' tx_locked es_locked es_locked' H_get H_locked.
    asm_opt_finalizer IN accepted_finalizers /\
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc,runtime_bc) /\
    deploy_typing_ok tops am_dep tx_dep /\
    deploy_state_rel tops deploy_bc am_dep tx_dep es_dep /\
    LENGTH (call_trace es_dep) < 2 ** 64 /\
    run_call es_dep = SOME (INR NONE,es_dep') /\
    call_trace es_dep = [] /\ gas_readings es_dep = [] /\
    deploy_storage_ok tops am_dep tx_dep [] [] /\
    load_contract (SOME []) [] am_dep tx_dep [(NONE,tops)] [] = INL (am_dep',[]) /\
    source_typing_ok tops (next_source_machine am_dep' es_dep') tx_get /\
    call_state_rel tops runtime_bc (next_source_machine am_dep' es_dep') tx_get es_get /\
    LENGTH (call_trace es_get) < 2 ** 64 /\
    storage_ok H_get (next_source_machine am_dep' es_dep') tx_get /\
    call_within H_get tops (next_source_machine am_dep' es_dep') tx_get es_get /\
    e2eDefs$valid_vyper_call tops tx_get
      (buffer_to_list (FST (HD es_get.contexts)).msgParams.data) (BaseT (UintT 256)) /\
    calldata_dispatch tops tx_get.calldata =
      SOME (tx_get.function_name,tx_get.args) /\
    call_trace es_get = [] /\ gas_readings es_get = [] /\
    run_call es_get = SOME (INR NONE,es_get') /\
    FST (call_external (SOME []) [] (next_source_machine am_dep' es_dep') tx_get) =
      INL (IntV 42) /\
    (FST (HD es_get'.contexts)).returnData = word_to_bytes (42w : bytes32) T /\
    source_typing_ok tops (next_source_machine am_dep' es_dep') tx_locked /\
    call_state_rel tops runtime_bc (next_source_machine am_dep' es_dep') tx_locked es_locked /\
    LENGTH (call_trace es_locked) < 2 ** 64 /\
    storage_ok H_locked (next_source_machine am_dep' es_dep') tx_locked /\
    call_within H_locked tops (next_source_machine am_dep' es_dep') tx_locked es_locked /\
    calldata_dispatch tops tx_locked.calldata =
      SOME (tx_locked.function_name,tx_locked.args) /\
    (?mut args dflts ret body.
      vyperInterpreter$lookup_function NONE tx_locked.function_name External tops =
        SOME (mut,T,args,dflts,ret,body)) /\
    call_trace es_locked = [] /\ gas_readings es_locked = [] /\
    run_call es_locked = SOME (INR NONE,es_locked') /\
    FST (call_external (SOME []) [] (next_source_machine am_dep' es_dep') tx_locked) =
      INL (IntV 43) /\
    (FST (HD es_locked'.contexts)).returnData = word_to_bytes (43w : bytes32) T
Proof
  MAP_EVERY exists_tac witnesses >>
  rewrite_tac (deploy_premises @ [dep_bound, deploy_guard,
         dep_run, dep_trace, load, get_trace, get_run, optimized_getter_valid,
         locked_trace, locked_run] @
        get_facts @ locked_facts @ get_storage @ locked_storage @ call_facts) >>
  simp[]
QED

local
  val runtime_parsed = cv_eval ``parse_code 0 FEMPTY ^runtime_bc``
  val runtime_call_free = SIMP_RULE (srw_ss())
    [listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST] (EQT_ELIM
      ((REWRITE_CONV [runtime_parsed, rich_listTheory.COUNT_LIST_GENLIST] THENC EVAL) ``
        EVERY (\pc. ~MEM (FLOOKUP (parse_code 0 FEMPTY ^runtime_bc) pc)
          [SOME Call; SOME StaticCall; SOME DelegateCall; SOME Create; SOME Create2])
          (COUNT_LIST (LENGTH ^runtime_bc))``))

  val dispatch_facts = map EVAL [
    ``calldata_dispatch ^tops (^get_tx).calldata``,
    ``calldata_dispatch ^tops (^locked_tx).calldata``,
    ``vyperInterpreter$lookup_function NONE "locked_get" External ^tops``]
  fun selected_source_facts (tx, name) =
    let
      val selected = ``^tx with <| function_name := ^name; args := [] |>``
    in
      map (SIMP_RULE (srw_ss()) [] o EVAL) [
        ``call_storage_ok ^am_call ^selected [] gs``,
        ``FST (call_external (SOME []) obs ^am_call ^selected)``]
    end
  val gas_source_facts =
    selected_source_facts (get_tx, ``"get"``) @
    selected_source_facts (locked_tx, ``"locked_get"``)
in

(* Both selected calls meet the gas-sufficiency guards at every added gas. *)
Theorem asm_opt_nonreentrant_call_gas_sufficiency_nonvacuity:
  ?policy tops deploy_bc runtime_bc am tx_get es_get tx_locked es_locked.
    asm_opt_finalizer IN accepted_finalizers /\
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc,runtime_bc) /\
    source_typing_ok tops am tx_get /\ call_state_rel tops runtime_bc am tx_get es_get /\
    source_typing_ok tops am tx_locked /\ call_state_rel tops runtime_bc am tx_locked es_locked /\
    calldata_dispatch tops tx_get.calldata = SOME ("get",[]) /\
    calldata_dispatch tops tx_locked.calldata = SOME ("locked_get",[]) /\
    (?mut args dflts ret body.
      vyperInterpreter$lookup_function NONE "locked_get" External tops =
        SOME (mut,T,args,dflts,ret,body)) /\
    !tx es g' f vals.
      ((tx,es) = (tx_get,es_get) \/ (tx,es) = (tx_locked,es_locked)) /\
      calldata_dispatch tops tx.calldata = SOME (f,vals) ==>
      (!gs. call_storage_ok am
         (tx with <| function_name := f; args := vals |>)
         (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
      (!obs. ~gas_source_exempt tops
         (tx with <| function_name := f; args := vals |>)
         (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am (tx with <| function_name := f; args := vals |>))) /\
      LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64
Proof
  `!es. wf_state es /\
        (FST (HD es.contexts)).msgParams.code = ^runtime_bc /\
        (FST (HD es.contexts)).msgParams.parsed = parse_code 0 FEMPTY ^runtime_bc ==>
        call_trace es = []` by (
    rpt strip_tac >>
    Cases_on `call_trace es` >> simp[] >>
    rename1 `call_trace es = entry :: _` >>
    PairCases_on `entry` >>
    rename1 `call_trace es = (rq,oc) :: _` >>
    `MEM (rq,oc) (call_trace es)` by simp[] >>
    drule_all call_trace_entry_origin >> strip_tac >>
    rename1 `run_call_reaches es reached` >>
    `(FST (HD reached.contexts)).msgParams = (FST (HD es.contexts)).msgParams`
      by (irule run_call_reaches_root_msgParams >> asm_rewrite_tac[]) >>
    qpat_x_assum `observable_call _` mp_tac >>
    simp[observable_call_def, next_opcode_def] >>
    IF_CASES_TAC >> simp[] >>
    qspec_then `(FST (HD reached.contexts)).pc` mp_tac runtime_call_free >>
    fs[arithmeticTheory.NOT_LE] >> metis_tac[]) >>
  `wf_state ^get_es /\ wf_state ^locked_es` by (
    mp_tac (List.nth (get_facts, 1)) >> mp_tac (List.nth (locked_facts, 1)) >>
    simp[call_state_rel_def, evm_state_ok_def]) >>
  `!g. call_trace (add_frame_gas g ^get_es) = [] /\
       call_trace (add_frame_gas g ^locked_es) = []` by (
    gen_tac >> conj_tac >> first_x_assum irule >>
    (conj_tac
     >- (irule add_frame_gas_wf_state >> asm_rewrite_tac[]) >>
     simp[add_frame_gas_def, p23_frame_def])) >>
  MAP_EVERY exists_tac
    [``o1_policy all_capabilities``, tops, deploy_bc, runtime_bc, am_call,
     get_tx, get_es, locked_tx, locked_es] >>
  rewrite_tac (common_premises @ get_facts @ locked_facts @ dispatch_facts) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs (dispatch_facts @ gas_source_facts @ [gas_source_exempt_def, source_exempt_def])
QED

end
end

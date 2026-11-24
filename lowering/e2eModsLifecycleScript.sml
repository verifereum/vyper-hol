(* Deployment supplies the installed code and the source premises of a
 * subsequent call to the same linked contract. *)
Theory e2eModsLifecycle
Ancestors
  e2eLifecycle e2eModsDefs e2eDeployModsDefs e2eDefs e2eComposition
  e2eTransactionWorld
  vyperContext vyperInterpreter vyperState vyperTypeContract
  vyperTypeContractSoundness vyperTypeDeploymentMachine
  vyperTypeContractModes[qualified]
  vyperTypeInitialState vyperTypeInvariants vyperDeployConstantsFoldMods
  vfmState vfmExecution vfmRunCall vfmTotalBalance callTrace
  e2eCodeFrame vyperLinkedRuntimeImmutables alist finite_map

Definition call_ready_mods_def:
  call_ready_mods mods exps runtime_bc am a <=>
    am.logs = [] /\ am.pending_deletions = [] /\
    installed_code_rel_mods mods runtime_bc (account_immutables am a)
      (lookup_account a am.accounts).code /\
    !tx. tx.target = a /\ call_tx_well_typed tx ==>
         source_typing_ok_mods mods exps am tx /\
         source_deployment_rel_mods mods exps am tx
End

Theorem call_ready_mods_singleton:
  call_ready_mods [(NONE, tops)] [] = call_ready tops
Proof
  simp[FUN_EQ_THM, call_ready_mods_def, call_ready_def,
       installed_code_rel_mods_singleton, source_typing_ok_mods_singleton,
       source_deployment_rel_mods_singleton]
QED

Triviality deployed_sources_layouts:
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  am'.sources <> am.sources ==>
  am'.sources = (tx.target, mods) :: am.sources /\ am'.layouts = am.layouts
Proof
  strip_tac >>
  drule_all load_contract_success_constructor_constants_context >>
  strip_tac >>
  drule call_external_function_preserves_sources >> simp[]
QED

Triviality deploy_typing_mods_checker:
  deploy_typing_ok_mods mods exps am tx ==>
  ?deploy_art runtime_art.
    check_contract T am.layouts tx.target mods = SOME deploy_art /\
    check_contract F am.layouts tx.target mods = SOME runtime_art /\
    exports_ok am.layouts tx.target mods exps /\
    machine_well_typed am /\ call_tx_well_typed tx
Proof
  simp[deploy_typing_ok_mods_def] >>
  metis_tac[vyperTypeContractModesTheory.check_contract_deploy_implies_runtime]
QED

Triviality deploy_typing_mods_ownership:
  deploy_typing_ok_mods mods exps am tx ==>
  linked_state_ownership_ok am.layouts tx.target mods exps
Proof
  simp[deploy_typing_ok_mods_def] >>
  metis_tac[check_contract_linked_state_ownership_ok]
QED

Triviality layouts_agree_mods_cong:
  am2.layouts = am1.layouts /\ tx2.target = tx1.target ==>
  (layouts_agree_mods mods exps am2 tx2 <=> layouts_agree_mods mods exps am1 tx1)
Proof
  simp[layouts_agree_mods_def]
QED

Triviality deployed_global_cells_typed:
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  am'.sources <> am.sources /\
  ALOOKUP am'.sources tx.target = SOME mods /\
  check_contract F am'.layouts tx.target mods = SOME art ==>
  global_cells_typed_mods mods art.cta_bare_globals (account_immutables am' tx.target)
Proof
  strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`call_tx` |-> `deploy_tx`]
    load_contract_establishes_immutables_ready)) >>
  simp[immutables_ready_def, get_tenv_def, initial_evaluation_context_def,
       account_immutables_def, empty_immutables_def, global_cells_typed_mods_def] >>
  metis_tac[optionTheory.IS_SOME_EXISTS, pairTheory.PAIR]
QED

Theorem deploy_establishes_call_ready_mods:
  deploy_typing_ok_mods mods exps am tx /\
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  deploy_result_rel_mods H mods runtime_bc tx es r es' (INL (am', rqs)) ==>
  call_ready_mods mods exps runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  drule deploy_typing_mods_checker >> strip_tac >>
  drule deploy_typing_mods_ownership >> strip_tac >>
  `wf_state es /\ ALOOKUP am.sources tx.target = NONE /\
   ALOOKUP mods NONE <> NONE /\ layouts_agree_mods mods exps am tx` by
    fs[deploy_state_rel_mods_def] >>
  `am'.sources <> am.sources` by (strip_tac >> gvs[deploy_result_rel_mods_def]) >>
  drule_all deployed_sources_layouts >> strip_tac >>
  `?main. ALOOKUP mods NONE = SOME main` by
    (Cases_on `ALOOKUP mods NONE` >> gvs[]) >>
  `context_well_typed
     (initial_evaluation_context ((tx.target, mods) :: am.sources)
        am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` by
    fs[context_well_typed_def, initial_evaluation_context_def, call_tx_well_typed_def] >>
  drule_all load_contract_establishes_machine_well_typed >> strip_tac >>
  drule_all load_contract_establishes_constants_fold_mods >> strip_tac >>
  drule load_contract_deployed_exports >> strip_tac >>
  `accounts_well_typed es'.rollback.accounts` by
    (irule run_call_accounts_well_typed >> goal_assum $ drule_at Any >> simp[]) >>
  `machine_well_typed (next_source_machine am' es')` by
    (irule next_source_machine_well_typed >> fs[machine_well_typed_def]) >>
  `global_cells_typed_mods mods runtime_art.cta_bare_globals
     (account_immutables am' tx.target)` by
    (irule deployed_global_cells_typed >> simp[] >>
     qexistsl [`am`, `exps`, `gs`, `orc`, `rqs`] >> simp[]) >>
  simp[call_ready_mods_def] >> conj_tac
  >- (gvs[deploy_result_rel_mods_def, installed_code_rel_mods_def,
          lookup_account_process_deletions] >> metis_tac[]) >>
  qx_gen_tac `call_tx` >> strip_tac >>
  `layouts_agree_mods mods exps (next_source_machine am' es') call_tx` by
    metis_tac[layouts_agree_mods_cong, next_source_machine_fields] >>
  conj_tac
  >- gvs[Once source_typing_ok_mods_def, account_immutables_def] >>
  fs[source_deployment_rel_mods_def]
QED

Theorem deploy_call_result_establishes_call_ready_mods:
  deploy_typing_ok_mods mods exps am tx /\
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  deploy_call_result_rel_mods mods exps runtime_bc am tx es r es' ==>
  gas_readings_rel (gas_readings es)
    (\gs. deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace es)) gs ==>
          !am' rqs.
            load_contract (SOME (MAP SND (call_trace es))) gs am tx
              mods exps = INL (am', rqs) ==>
            call_ready_mods mods exps runtime_bc (next_source_machine am' es')
              tx.target)
Proof
  rw[deploy_call_result_rel_mods_def] >>
  irule gas_readings_rel_mono >> goal_assum (drule_at Any) >>
  rw[] >> irule (INST_TYPE [alpha |-> “:256”] deploy_establishes_call_ready_mods) >>
  rpt (conj_tac >- simp[]) >>
  qexistsl_tac [`storage_trace_horizon (deploy_storage_trace_mods
                   (SOME (MAP SND (call_trace es))) gs am tx mods exps)`,
                `am`, `deploy_bc`, `es`, `gs`, `SOME (MAP SND (call_trace es))`,
                `r`, `rqs`] >>
  gvs[]
QED

(* Ownership depends on the layout and target, which the call preserves. *)
Triviality call_preserves_linked_ownership:
  source_typing_ok_mods mods exps am tx /\
  am'.layouts = am.layouts ==>
  linked_state_ownership_ok (next_source_machine am' es').layouts tx.target
    mods exps
Proof
  simp[source_typing_ok_mods_def] >>
  metis_tac[check_contract_linked_state_ownership_ok]
QED

Theorem call_preserves_call_ready_mods:
  call_ready_mods mods exps runtime_bc am tx.target /\ call_tx_well_typed tx /\
  runtime_bc <> [] /\
  call_state_rel_mods mods exps runtime_bc am tx es /\ LENGTH es.contexts = 1 /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  call_ready_mods mods exps runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  `source_typing_ok_mods mods exps am tx /\
   source_deployment_rel_mods mods exps am tx` by
    fs[call_ready_mods_def] >>
  `am'.immutables = am.immutables` by
    (irule call_external_runtime_mods_preserves_immutables >>
     fs[source_typing_ok_mods_def, source_deployment_rel_mods_def] >>
     metis_tac[]) >>
  drule call_external_static_fields >> strip_tac >>
  `?ctxt rb rest mr.
     es.contexts = (ctxt, rb) :: rest /\ wf_state es /\
     ctxt.msgParams.outputTo = Memory mr /\
     installed_code_rel_mods mods runtime_bc (account_immutables am tx.target)
       ctxt.msgParams.code /\
     (lookup_account tx.target es.rollback.accounts).code =
       ctxt.msgParams.code` by
    (fs[call_state_rel_mods_def, evm_state_ok_def] >> metis_tac[]) >>
  `accounts_well_typed es'.rollback.accounts` by
    (irule run_call_accounts_well_typed >> goal_assum $ drule_at Any >> simp[]) >>
  `(lookup_account tx.target es'.rollback.accounts).code =
   (lookup_account tx.target es.rollback.accounts).code` by
    (irule run_call_preserves_installed_code >>
     gvs[installed_code_rel_mods_def] >> metis_tac[]) >>
  `machine_well_typed (next_source_machine am' es')` by
    (irule next_source_machine_well_typed >>
     fs[source_typing_ok_mods_def, machine_well_typed_def]) >>
  simp[call_ready_mods_def] >> conj_tac
  >- (gvs[lookup_account_process_deletions] >> fs[account_immutables_def]) >>
  qx_gen_tac `tx2` >> strip_tac >>
  `source_typing_ok_mods mods exps am tx2 /\
   source_deployment_rel_mods mods exps am tx2` by
    fs[call_ready_mods_def] >>
  `linked_state_ownership_ok (next_source_machine am' es').layouts
     tx2.target mods exps` by
    (irule call_preserves_linked_ownership >> metis_tac[]) >>
  `layouts_agree_mods mods exps (next_source_machine am' es') tx2` by
    metis_tac[layouts_agree_mods_cong, next_source_machine_fields,
              source_deployment_rel_mods_def] >>
  fs[source_typing_ok_mods_def, source_deployment_rel_mods_def,
     account_immutables_def] >>
  gvs[]
QED

Theorem call_external_next_source_machine_mods:
  source_typing_ok_mods mods exps am tx /\
  source_deployment_rel_mods mods exps am tx /\
  call_external orc gs am tx = (res, am', rqs) ==>
  next_source_machine am' es' = next_source_machine am es'
Proof
  strip_tac >>
  `am'.immutables = am.immutables` by
    (irule call_external_runtime_mods_preserves_immutables >>
     fs[source_typing_ok_mods_def, source_deployment_rel_mods_def] >>
     metis_tac[]) >>
  drule call_external_static_fields >>
  simp[next_source_machine_def, abstract_machine_component_equality]
QED

Theorem call_preserves_transaction_world_mods:
  call_ready_mods mods exps runtime_bc am tx.target /\
  call_tx_well_typed tx /\
  runtime_bc <> [] /\
  call_state_rel_mods mods exps runtime_bc am tx es /\ LENGTH es.contexts = 1 /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete ==>
  call_ready_mods mods exps runtime_bc (transaction_world am r es') tx.target
Proof
  strip_tac >> Cases_on `r = INR NONE` >> simp[transaction_world_def] >>
  `source_typing_ok_mods mods exps am tx /\
   source_deployment_rel_mods mods exps am tx` by fs[call_ready_mods_def] >>
  Cases_on `call_external NONE [] am tx` >>
  rename1 `call_external NONE [] am tx = (res, output)` >>
  PairCases_on `output` >>
  rename1 `call_external NONE [] am tx = (res, am_out, rqs)` >>
  `next_source_machine am_out es' = next_source_machine am es'` by
    (irule call_external_next_source_machine_mods >> metis_tac[]) >>
  drule_all call_preserves_call_ready_mods >> simp[]
QED

Theorem transaction_sequence_call_ready_mods:
  LENGTH worlds = SUC (LENGTH calls) /\
  call_ready_mods mods exps runtime_bc (HD worlds) a /\
  runtime_bc <> [] /\
  (!i tx ret H es r es'.
    i < LENGTH calls /\ EL i calls = (tx, ret, H, es, r, es') /\
    call_ready_mods mods exps runtime_bc (EL i worlds) a ==>
    tx.target = a /\ call_tx_well_typed tx /\
    call_state_rel_mods mods exps runtime_bc (EL i worlds) tx es /\
    LENGTH es.contexts = 1 /\ balance_bounded (2 ** 256 - 1) es /\
    run_call es = SOME (r, es') /\ ~MEM a es'.rollback.toDelete /\
    EL (SUC i) worlds = transaction_world (EL i worlds) r es') ==>
  EVERY (\am. call_ready_mods mods exps runtime_bc am a) worlds
Proof
  strip_tac >>
  `!i. i < LENGTH worlds ==> call_ready_mods mods exps runtime_bc (EL i worlds) a` by
    (Induct >- (Cases_on `worlds` >> gvs[]) >> strip_tac >>
     `i < LENGTH calls /\ i < LENGTH worlds` by decide_tac >>
     `call_ready_mods mods exps runtime_bc (EL i worlds) a` by metis_tac[] >>
     Cases_on `EL i calls` >> rename1 `EL i calls = (tx, tail)` >>
     PairCases_on `tail` >>
     rename1 `EL i calls = (tx, ret, H, es, r, es')` >>
     `tx.target = a /\ call_tx_well_typed tx /\
      call_state_rel_mods mods exps runtime_bc (EL i worlds) tx es /\
      LENGTH es.contexts = 1 /\ balance_bounded (2 ** 256 - 1) es /\
      run_call es = SOME (r, es') /\ ~MEM a es'.rollback.toDelete /\
      EL (SUC i) worlds = transaction_world (EL i worlds) r es'` by
       metis_tac[] >>
     metis_tac[call_preserves_transaction_world_mods]) >>
  simp[listTheory.EVERY_EL]
QED

Theorem transaction_world_storage_handoff_mods:
  source_typing_ok_mods mods exps am tx /\
  source_deployment_rel_mods mods exps am tx /\
  call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
    (res, am', rqs, obs) /\
  H = storage_trace_horizon obs /\
  valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H obs /\
  am.tStorage tx.target = empty_storage /\
  LENGTH es.contexts = 1 /\ run_call es = SOME (r, es') /\
  ~source_exempt_mods mods (call_external (SOME (MAP SND (call_trace es))) gs am tx) /\
  (r = INR NONE ==>
    call_result_rel_at_mods gs mods exps am tx es r es' /\
    ~MEM tx.target es'.rollback.toDelete) /\
  cx2.txn.target = tx.target /\
  (!slot tv. MEM (F, slot, tv) R2 /\ ~MEM (F, slot, tv) (FST H) ==>
    slots_in_range
      (lookup_account tx.target (transaction_world am r es').accounts).storage
      (w2n slot) tv) ==>
  storage_well_formed_on cx2 (initial_state (transaction_world am r es') []) R2 /\
  (transaction_world am r es').tStorage tx.target = empty_storage
Proof
  strip_tac >> reverse conj_tac
  >- (irule transaction_world_transient_empty >> simp[]) >>
  reverse (Cases_on `r = INR NONE`) >> gvs[]
  >- suspend "unchanged_world" >>
  `call_external (SOME (MAP SND (call_trace es))) gs am tx =
    (res, am', rqs)` by simp[call_external_def] >>
  `source_storage_trace am tx (MAP SND (call_trace es)) gs = obs` by
    simp[source_storage_trace_def] >>
  `next_source_machine am' es' = next_source_machine am es'` by
    (irule call_external_next_source_machine_mods >> metis_tac[]) >>
  `?art. check_contract F am.layouts tx.target mods = SOME art /\
         checked_contract_runtime_ready art mods am tx /\
         machine_well_typed am /\ call_tx_well_typed tx` by
    suspend "runtime_ready" >>
  `storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am' []) (FST (storage_trace_horizon obs))` by
    (irule vyperCallFiniteStorageTheory.call_external_storage_well_formed_on >>
     metis_tac[]) >>
  `accounts_agree (storage_trace_horizon obs) tx.target am'.accounts
    (process_deletions es'.rollback.toDelete es'.rollback.accounts)` by
    suspend "committed_accounts" >>
  suspend "extend_horizon"
QED

Resume transaction_world_storage_handoff_mods[unchanged_world]:
  rw[transaction_world_def, vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  rename1 `MEM (tr, slot, tv) R2` >> Cases_on `tr`
  >- (simp[vyperStorageBackendTheory.get_storage_def, vyperInterpreterTheory.initial_state_def] >>
      irule (CONJUNCT1 vyperLookupStorageTheory.slots_in_range_zero_reads) >>
      simp[vyperStorageTheory.read_slot_def, lookup_storage_def, empty_storage_def]) >>
  Cases_on `MEM (F, slot, tv) (FST (storage_trace_horizon obs))` >>
  gvs[transaction_world_def, lookup_account_def, vyperStorageBackendTheory.get_storage_def,
      vyperInterpreterTheory.initial_state_def] >>
  fs[vyperStorageFootprintTheory.valid_horizon_def,
     vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  qpat_x_assum `!b slot tv. MEM (b, slot, tv) _ ==> _`
    (qspecl_then [`F`, `slot`, `tv`] mp_tac) >>
  simp[vyperStorageBackendTheory.get_storage_def, vyperInterpreterTheory.initial_state_def,
       initial_evaluation_context_def]
QED

Resume transaction_world_storage_handoff_mods[runtime_ready]:
  fs[source_typing_ok_mods_def, global_cells_typed_mods_def] >>
  `ALOOKUP am.sources tx.target = SOME mods /\
   (case ALOOKUP am.exports tx.target of NONE => [] | SOME xs => xs) = exps` by
    (fs[source_deployment_rel_mods_def] >>
     Cases_on `ALOOKUP am.exports tx.target` >> gvs[]) >>
  simp[checked_contract_runtime_ready_def] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`addr` |-> `tx.target`]
    vyperTypeContractStaticMapsTheory.check_contract_toplevel_vtypes_consistent_initial)) >>
  simp[get_module_code_def, initial_evaluation_context_def] >> strip_tac >>
  drule vyperTypeContractStaticMapsTheory.check_contract_bare_globals_consistent_initial >>
  disch_then (qspecl_then [`tx`, `am.sources`] mp_tac) >>
  simp[get_module_code_def, initial_evaluation_context_def] >> strip_tac >>
  fs[account_immutables_def, empty_immutables_def] >>
  simp[immutables_ready_def, get_tenv_def, get_module_code_def,
       initial_evaluation_context_def] >>
  conj_tac >- metis_tac[optionTheory.IS_SOME_EXISTS] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!src id ty. FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==> ?tv v. _` drule >>
      strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty)` >>
  Cases_on `FLOOKUP art.cta_bare_globals (src,id)`
  >- (qpat_x_assum `!src id ty. _ /\ FLOOKUP art.cta_bare_globals (src,id) = NONE ==> _`
        (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
      simp[] >> strip_tac >> gvs[]) >>
  rename1 `FLOOKUP art.cta_bare_globals (src,id) = SOME bare_ty` >>
  qpat_x_assum `!src id ty. _ ==> ?ts. _ /\ FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ _`
    (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!src id ty. FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==> ?tv v. _`
    (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
  simp[]
QED

Resume transaction_world_storage_handoff_mods[committed_accounts]:
  namedCases_on `res` ["v", "source_exc"] >>
  gvs[call_result_rel_at_mods_def, effects_agree_def, LET_THM] >>
  Cases_on `source_exc` >>
  gvs[exception_outcome_rel_mods_def, source_exempt_mods_def,
      frameOutcomeTheory.frame_outcome_def, AllCaseEqs()]
QED

Resume transaction_world_storage_handoff_mods[extend_horizon]:
  qabbrev_tac `D = storage_dead (storage_trace_horizon obs) F
    (lookup_account tx.target am'.accounts).storage` >>
  `lookup_account tx.target
    (process_deletions es'.rollback.toDelete es'.rollback.accounts) =
   lookup_account tx.target es'.rollback.accounts` by
    simp[lookup_account_process_deletions] >>
  `storage_agree D (lookup_account tx.target am'.accounts).storage
    (lookup_account tx.target es'.rollback.accounts).storage` by
    fs[loweringStateRelDefsTheory.accounts_agree_def, GSYM lookup_account_def,
       Abbr `D`] >>
  `!j b slot tv. D j b /\ MEM (F, slot, tv) (FST (storage_trace_horizon obs)) /\
    w2n slot <= j /\ j < w2n slot + type_slot_size tv ==>
    dead_bytes (lookup_account tx.target am'.accounts).storage
      (w2n slot) tv j b` by
    (rw[Abbr `D`] >>
     drule accountsRelPropsTheory.observed_storage_region_read_live >>
     simp[loweringStateRelDefsTheory.storage_read_live_def] >> metis_tac[]) >>
  `!slot tv. MEM (F, slot, tv) R2 /\ ~MEM (F, slot, tv) (FST (storage_trace_horizon obs)) ==>
    slots_in_range (lookup_account tx.target es'.rollback.accounts).storage
      (w2n slot) tv` by
    fs[transaction_world_def, next_source_machine_def,
       lookup_account_process_deletions] >>
  `regions_consistent (FST (storage_trace_horizon obs))` by
    fs[vyperStorageFootprintTheory.valid_horizon_def] >>
  mp_tac (Q.INST
    [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
     `R1` |-> `FST (storage_trace_horizon obs)`, `D` |-> `D`]
    storage_well_formed_on_horizon_extension) >>
  (impl_tac >- gvs[initial_evaluation_context_def]) >>
  simp[transaction_world_def]
QED

Finalise transaction_world_storage_handoff_mods

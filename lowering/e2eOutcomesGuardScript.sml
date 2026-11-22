(* Closed-world storage invariants for a reentered frame. *)
Theory e2eOutcomesGuard
Ancestors
  e2eRequestCutDefs e2eDefs vfmAccountFrame vyperStorageFootprint
  vyperInterpreter vyperState vyperStorageBackend vfmState vfmContext
  callTraceFrameProvenance callTraceFrame callTrace guardReentryCode guardReentryAccounts
  guardPushProjections immutableSectionRel vfmExecution vfmExecutionProp
  e2eCorrectness e2eComposition e2eProducers frameOutcome callGuardGasLinkProof
  e2eOptEntry immutableCodeLayout ownSymSrcUnit o1PipelineCompose
  asmFrameRel unitTransformDefs
  guardTerminalBackend guardSourceAlignment asmOptimizer asmOptNonemptyFinalizer
  vfmAccountDeletion e2eEntry
  vyperCallFiniteStorageSupport guardRequestCutAlignment loweringCalldataCorrect
  callRawVariant sourceUnitExecution vyperLoweringCorrect gasSummary
  stackPlanGen
  vfmDecreasesGas relation pair arithmetic list
  gasFocusPacketPipelineStages requestCutSelectedReplay
  gasMaskProjection gasEvents gasExplicitSites
  venomState sorting
Libs
  stepInstBaseLib

Triviality guard_closed_world_inherit:
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  run_call_reaches es e /\ LENGTH es.contexts <= LENGTH e.contexts /\
  am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
  tx_e.target = tx.target /\
  world_rel am_e tx_e e /\
  storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (empty_state with <|accounts := e.rollback.accounts;
                       tStorage := e.rollback.tStorage|>) (FST H) /\
  horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
  ~account_empty (lookup_account tx_e.target e.originalAccounts) /\
  (!gobs. ~source_exempt tops
    (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e)) ==>
  vyper_closed_world fin policy tops runtime_bc am_e tx_e H e
Proof
  strip_tac >>
  `!a. (accounts_after_transfer tx_e am_e.accounts a).storage =
       (am_e.accounts a).storage` by
    (gen_tac >> rw[accounts_after_transfer_def, lookup_account_def,
                  update_account_def, combinTheory.APPLY_UPDATE_THM] >>
     rpt IF_CASES_TAC >> simp[]) >>
  `storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (initial_state am_e []) (FST H)` by
    (qpat_x_assum `world_rel _ _ _`
       (strip_assume_tac o REWRITE_RULE [world_rel_def]) >>
     qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[storage_well_formed_on_def, boolTheory.FORALL_BOOL,
          get_storage_def, vyperInterpreterTheory.initial_state_def]) >>
  fs[vyper_closed_world_def] >> rpt strip_tac >>
  rename1 `step s = (INL u, child)` >>
  `run_call_reaches es s` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[]) >>
  qpat_x_assum `!s child. run_call_reaches es s /\ _ ==> _`
    (qspecl_then [`s`, `child`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

Triviality guard_closed_world_storage_at_readings:
  vyper_frame_staging fin policy tops runtime_bc am tx es /\
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
    (res,am',rqs,obs) /\
  (!pre rq co sfx.
    obs = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) H pre ==>
    (co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage) \/
    ?rq'. MEM (rq',co) (call_trace es) /\ request_agree H tx.target rq rq') /\
  (!rq co.
    MEM (rq,co) (call_trace es) /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H)) ==>
  call_storage_ok am tx (MAP SND (call_trace es)) gs /\
  storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am' []) (FST H)
Proof
  strip_tac >>
  `source_typing_ok tops am tx /\ source_deployment_rel tops am tx` by
    fs[vyper_frame_staging_def, call_state_rel_def] >>
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
   storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) (FST H) /\
   horizon_covers H am tx (MAP SND (call_trace es))` by
    fs[vyper_closed_world_def] >>
  drule call_external_trace_result >> strip_tac >>
  `EVERY (\r. MEM r (FST H)) (storage_trace_regions obs) /\
   EVERY (\l. MEM l (SND H)) (storage_trace_locks obs) /\ storage_roots_fit obs` by
    (qpat_assum `horizon_covers _ _ _ _`
      (mp_tac o Q.SPEC `gs` o REWRITE_RULE [horizon_covers_def]) >> simp[]) >>
  `(initial_evaluation_context am.sources am.layouts tx NONE).txn.target = tx.target` by
    simp[initial_evaluation_context_def] >>
  `storage_observations_ok (initial_evaluation_context am.sources am.layouts tx NONE) H obs` by
    (mp_tac (Q.INST [`os` |-> `MAP SND (call_trace es)`, `trace` |-> `call_trace es`,
       `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`]
       aligned_trace_storage_observations) >> asm_rewrite_tac[]) >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) H obs` by simp[valid_horizon_def] >>
  conj_tac
  >- (irule valid_horizon_call_storage_ok >> qexists_tac `H` >> simp[]) >>
  drule_all source_call_final_storage_well_formed >> simp[]
QED

Triviality guard_close_storage_readings:
  vyper_frame_staging fin policy tops runtime_bc am tx es /\
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  (!rq co.
    MEM (rq,co) (call_trace es) /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H)) /\
  gas_readings_rel (gas_readings es)
    (\gs.
       (call_storage_ok am tx (MAP SND (call_trace es)) gs ==>
        call_result_rel_at gs tops am tx es r es') /\
       !res am' rqs obs pre rq co sfx.
         call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
           (res,am',rqs,obs) /\
         obs = pre ++ StorageOutcome rq co :: sfx /\
         valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
           (initial_state am []) H pre ==>
         (co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage) \/
         ?rq'. MEM (rq',co) (call_trace es) /\ request_agree H tx.target rq rq') ==>
  gas_readings_rel (gas_readings es)
    (\gs. call_storage_ok am tx (MAP SND (call_trace es)) gs /\
      call_result_rel_at gs tops am tx es r es' /\
      ?res am' rqs obs.
        call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
          (res,am',rqs,obs) /\
        storage_well_formed_on
          (initial_evaluation_context am.sources am.layouts tx NONE)
          (initial_state am' []) (FST H))
Proof
  strip_tac >>
  qpat_x_assum `gas_readings_rel _ _` (fn bridge =>
    match_mp_tac (MATCH_MP
      (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_readings_rel_mono) bridge)) >>
  qx_gen_tac `gs` >> BETA_TAC >> strip_tac >>
  `?res am' rqs obs.
    call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
      (res,am',rqs,obs)` by metis_tac[ABS_PAIR_THM] >>
  mp_tac guard_closed_world_storage_at_readings >>
  impl_tac
  >- (asm_simp_tac bool_ss [] >> conj_tac
      >- (map_every qx_gen_tac [`pre`, `rq`, `co`, `sfx`] >> strip_tac >>
          qpat_assum `!res am' rqs obs pre rq co sfx. _`
            (qspecl_then [`res`, `am'`, `rqs`, `obs`, `pre`, `rq`, `co`, `sfx`] mp_tac) >>
          asm_simp_tac bool_ss []) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> simp[] >> metis_tac[]
QED

Triviality guard_frame_runtime_nonempty:
  vyper_frame_staging fin policy tops runtime_bc am tx es ==>
  runtime_bc <> []
Proof
  strip_tac >> fs[vyper_frame_staging_def, accepted_finalizers_def]
  >- (gvs[] >> metis_tac[compile_vyper_runtime_nonempty]) >>
  gvs[] >> drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  gvs[] >> metis_tac[codegen_assembly_finalizer_nonempty]
QED

Triviality guard_staged_run_no_target_deletion:
  vyper_frame_staging fin policy tops runtime_bc am tx es /\
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  run_call es = SOME (r,es') /\
  ~MEM tx.target es.rollback.toDelete /\
  (2 <= LENGTH es.contexts ==> ~MEM tx.target (SND (HD es.contexts)).toDelete) ==>
  ~MEM tx.target es'.rollback.toDelete
Proof
  strip_tac >> drule guard_frame_runtime_nonempty >> strip_tac >>
  `wf_state es /\ ~NULL (lookup_account tx.target es.rollback.accounts).code` by
    (fs[vyper_frame_staging_def, call_state_rel_def, evm_state_ok_def,
        installed_code_rel_def, NULL_EQ] >> metis_tac[APPEND_eq_NIL]) >>
  `~account_empty (lookup_account tx.target es.originalAccounts)` by
    fs[vyper_closed_world_def] >>
  spose_not_then assume_tac >>
  drule_all run_call_to_delete >> simp[] >> metis_tac[]
QED

Triviality guard_reentry_staging:
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  call_state_rel tops runtime_bc am tx es /\ runtime_bc <> [] /\
  run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
  step s = (INL (),e) /\ LENGTH s.contexts < LENGTH e.contexts /\
  (FST (HD e.contexts)).msgParams.callee = tx.target /\
  ~(FST (HD e.contexts)).msgParams.static /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := e.rollback.accounts;
                       tStorage := e.rollback.tStorage|>) (FST H) ==>
  ?am_e tx_e.
    am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
    tx_e.target = tx.target /\
    vyper_frame_staging fin policy tops runtime_bc am_e tx_e e /\
    (calldata_dispatch tops (buffer_to_list (FST (HD e.contexts)).msgParams.data) = NONE \/
     vyper_closed_world fin policy tops runtime_bc am_e tx_e H e /\
     LENGTH (call_trace e) < 2 ** 64 /\
     ?ret_e. dispatched_vyper_call tops tx_e
       (buffer_to_list (FST (HD e.contexts)).msgParams.data) ret_e)
Proof
  strip_tac >>
  qpat_assum `vyper_closed_world _ _ _ _ _ _ _ _`
    (mp_tac o last o CONJUNCTS o REWRITE_RULE [vyper_closed_world_def]) >>
  disch_then (qspecl_then [`s`, `()`, `e`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `am_e` (qx_choose_then `tx_e`
    (map_every assume_tac o CONJUNCTS))) >>
  `tx_e.target = tx.target /\ world_rel am_e tx_e e` by
    (fs[vyper_frame_staging_def, call_state_rel_def, frame_tx_rel_def] >> gvs[]) >>
  `wf_state es /\ account_already_created (lookup_account tx.target es.rollback.accounts)` by
    (fs[call_state_rel_def, evm_state_ok_def, installed_code_rel_def,
        account_already_created_def, NULL_EQ] >> metis_tac[APPEND_eq_NIL]) >>
  `~account_empty (lookup_account tx.target es.originalAccounts)` by
    fs[vyper_closed_world_def] >>
  `run_call_reaches es e` by
    (irule run_call_reaches_step >> qexistsl_tac [`s`, `()`] >> simp[]) >>
  `LENGTH es.contexts <= LENGTH e.contexts` by decide_tac >>
  `~account_empty (lookup_account tx_e.target e.originalAccounts)` by
    (mp_tac (Q.INST [`s` |-> `e`, `a` |-> `tx.target`]
       guard_reaches_created_original_nonempty) >> simp[]) >>
  qexistsl_tac [`am_e`, `tx_e`] >> simp[] >>
  qpat_x_assum `calldata_dispatch _ _ = NONE \/ _` strip_assume_tac >> simp[] >>
  `storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (empty_state with <|accounts := e.rollback.accounts;
                       tStorage := e.rollback.tStorage|>) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
          initial_evaluation_context_def]) >>
  `vyper_closed_world fin policy tops runtime_bc am_e tx_e H e` by
    (mp_tac (Q.INST [`am` |-> `am`, `tx` |-> `tx`, `es` |-> `es`]
      guard_closed_world_inherit) >> simp[]) >>
  disj2_tac >> simp[] >> metis_tac[]
QED

val guard_frame_storage_pair =
  ``\cx (regions : (bool # bytes32 # type_value) list) p.
  ~NULL (FST p).code /\
  storage_well_formed_on cx
    (empty_state with <|accounts := K (FST p); tStorage := K (SND p)|>)
    regions``;

Triviality guard_trace_storage_from_reentries:
  call_state_rel tops runtime_bc am tx es /\ runtime_bc <> [] /\
  MEM (rq,co) (call_trace es) /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := rq.cr_accounts;
                       tStorage := rq.cr_tStorage|>) (regions : (bool # bytes32 # type_value) list) /\
  (!s u e r e'.
    run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
    wf_state s /\ wf_state e /\ step s = (INL u,e) /\
    LENGTH s.contexts < LENGTH e.contexts /\
    (FST (HD e.contexts)).msgParams.callee = tx.target /\
    ~(FST (HD e.contexts)).msgParams.static /\
    run_call e = SOME (r,e') /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := e.rollback.accounts;
                         tStorage := e.rollback.tStorage|>) regions /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := (SND (HD e.contexts)).accounts;
                         tStorage := (SND (HD e.contexts)).tStorage|>) regions ==>
    ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := e'.rollback.accounts;
                         tStorage := e'.rollback.tStorage|>) regions) ==>
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := co.co_accounts;
                       tStorage := co.co_tStorage|>) regions
Proof
  strip_tac >>
  `wf_state es /\
   (FST (HD es.contexts)).msgParams.callee = tx.target` by
    fs[call_state_rel_def, evm_state_ok_def, frame_tx_rel_def] >>
  `~NULL (lookup_account tx.target es.rollback.accounts).code` by
    (fs[call_state_rel_def, installed_code_rel_def, NULL_EQ] >>
     metis_tac[APPEND_eq_NIL]) >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `~NULL (lookup_account tx.target rq.cr_accounts).code` by
    (drule_all call_trace_entry_provenance >> strip_tac >> gvs[] >>
     irule guard_reaches_code_nonempty >> qexists_tac `es` >> simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `^guard_frame_storage_pair cx regions
    (lookup_account tx.target rq.cr_accounts, rq.cr_tStorage tx.target)` by
    (BETA_TAC >> fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
      lookup_account_def, Abbr `cx`, initial_evaluation_context_def]) >>
  `^guard_frame_storage_pair cx regions
    (lookup_account tx.target co.co_accounts, co.co_tStorage tx.target)`
    suffices_by
      (BETA_TAC >> fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
        lookup_account_def, Abbr `cx`, initial_evaluation_context_def]) >>
  BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  irule (BETA_RULE (Q.INST
    [`P` |-> `^guard_frame_storage_pair cx regions`, `a` |-> `tx.target`,
     `es` |-> `es`, `rq` |-> `rq`, `oc` |-> `co`]
    call_trace_account_transient_frame)) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def]) >>
  conj_tac
  >- (rpt gen_tac >> simp[foreign_account_change_def] >> strip_tac >>
      fs[account_already_created_def, storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def]) >>
  qexistsl_tac [`es`, `rq`] >> asm_rewrite_tac[] >>
  reverse conj_tac >- gvs[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?s. _`
    (qx_choose_then `s` (qx_choose_then `u` (map_every assume_tac o CONJUNCTS))) >>
  `2 <= LENGTH e.contexts` by decide_tac >>
  Cases_on `(FST (HD e.contexts)).msgParams.static`
  >- (mp_tac (Q.INST
        [`obs` |-> `\p. ^guard_frame_storage_pair cx regions
          (lookup_account tx.target (FST p), SND p tx.target)`,
         `e` |-> `e`, `e'` |-> `e'`, `r` |-> `r`]
        (INST_TYPE [alpha |-> ``:bool``] run_call_static_observation)) >>
      simp[] >> impl_tac
      >- (drule_all step_push_static_output_not_code >> fs[]) >>
      simp[]) >>
  qpat_x_assum `!s u e r e'. _`
    (qspecl_then [`s`, `u`, `e`, `r`, `e'`] mp_tac) >>
  impl_tac >-
    fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
       lookup_account_def, Abbr `cx`, initial_evaluation_context_def] >>
  strip_tac >>
  `run_call_reaches es e` by
    (irule run_call_reaches_step >> qexistsl_tac [`s`, `u`] >> simp[]) >>
  `LENGTH es.contexts <= LENGTH e.contexts` by decide_tac >>
  `run_call_reaches e e'` by
    (drule run_call_finite_trace >> strip_tac >>
     mp_tac (Q.SPEC `n` (Q.INST [`es` |-> `e`] run_call_trace_reaches)) >>
     simp[] >> metis_tac[]) >>
  `run_call_reaches es e'` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[]) >>
  `LENGTH es.contexts <= LENGTH e'.contexts` by decide_tac >>
  `~NULL (lookup_account tx.target e'.rollback.accounts).code` by
    (drule_all guard_reaches_code_nonempty >> simp[]) >>
  fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
     lookup_account_def, Abbr `cx`, initial_evaluation_context_def]
QED

Triviality guard_undispatched_reentry_rollback:
  vyper_frame_staging fin policy tops runtime_bc am tx e /\
  calldata_dispatch tops
    (buffer_to_list (FST (HD e.contexts)).msgParams.data) = NONE /\
  2 <= LENGTH e.contexts /\ run_call e = SOME (r,e') ==>
  ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
  e'.rollback = SND (HD e.contexts)
Proof
  strip_tac >> fs[vyper_frame_staging_def] >>
  drule_all vyper_call_reverts >>
  simp[frame_resource_starved_def] >>
  metis_tac[guard_nested_frame_outcome, optionTheory.NOT_SOME_NONE]
QED

Triviality guard_nested_call_result:
  2 <= LENGTH e.contexts /\
  call_external (SOME (MAP SND (call_trace e))) gs am tx = (res,am',rqs) /\
  ~source_exempt tops (res,am',rqs) /\
  call_result_rel_at gs tops am tx e r e' ==>
  ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts
Proof
  strip_tac >>
  `?exc out lgs. frame_outcome e r e' exc out lgs` suffices_by
    metis_tac[guard_nested_frame_outcome] >>
  qpat_x_assum `call_result_rel_at _ _ _ _ _ _ _` mp_tac >>
  simp[call_result_rel_at_def] >>
  Cases_on `res` >- (simp[] >> metis_tac[]) >>
  rename1 `INR exc` >> Cases_on `exc = HaltException`
  >- (gvs[] >> metis_tac[]) >>
  Cases_on `exc` >> simp[exception_outcome_rel_def] >>
  strip_tac >> gvs[source_exempt_def] >> metis_tac[]
QED

Triviality guard_nested_result_storage:
  vyper_closed_world fin policy tops runtime_bc am tx H e /\
  2 <= LENGTH e.contexts /\
  call_external_trace (SOME (MAP SND (call_trace e))) gs am tx =
    (res,am',rqs,obs) /\
  call_result_rel_at gs tops am tx e r e' /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am' []) (FST H) /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := (SND (HD e.contexts)).accounts;
                       tStorage := (SND (HD e.contexts)).tStorage|>) (FST H) /\
  ~MEM tx.target e'.rollback.toDelete ==>
  ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) (FST H)
Proof
  strip_tac >>
  drule call_external_trace_result >> strip_tac >>
  `regions_consistent (FST H) /\
   horizon_covers H am tx (MAP SND (call_trace e)) /\
   ~source_exempt tops (res,am',rqs)` by
    (fs[vyper_closed_world_def] >>
     qpat_assum `call_external _ gs am tx = (res,am',rqs)` (fn result =>
       qpat_assum `!gobs. ~source_exempt _ (call_external _ _ _ _)`
         (qspec_then `gs` (ACCEPT_TAC o REWRITE_RULE [result])))) >>
  `EVERY (\region. MEM region (FST H)) (storage_trace_regions obs)` by
    (qpat_assum `horizon_covers _ _ _ _`
      (mp_tac o Q.SPEC `gs` o REWRITE_RULE [horizon_covers_def]) >> simp[]) >>
  `(initial_evaluation_context am.sources am.layouts tx NONE).txn.target = tx.target` by
    simp[initial_evaluation_context_def] >>
  `ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts` by
    metis_tac[guard_nested_call_result] >>
  asm_rewrite_tac[] >>
  mp_tac (Q.INST [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`]
    (INST_TYPE [alpha |-> ``:num list``] guard_terminal_backend_well_formed)) >>
  simp[]
QED

Triviality guard_gas_readings_witness:
  gas_readings_rel readings P ==> ?gs. P gs
Proof
  rw[gas_readings_rel_def] >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots (MAP THE slots)` by
    (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     Cases_on `EL n slots` >> simp[]) >>
  qpat_x_assum `!gobs tail. _` (qspecl_then [`MAP THE slots`, `[]`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Triviality guard_nested_storage_from_readings:
  vyper_closed_world fin policy tops runtime_bc am tx H e /\
  2 <= LENGTH e.contexts /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := (SND (HD e.contexts)).accounts;
                       tStorage := (SND (HD e.contexts)).tStorage|>) (FST H) /\
  ~MEM tx.target e'.rollback.toDelete /\
  (frame_resource_starved e r e' \/
   gas_readings_rel (gas_readings e)
     (\gs. call_result_rel_at gs tops am tx e r e' /\
       ?res am' rqs obs.
         call_external_trace (SOME (MAP SND (call_trace e))) gs am tx =
           (res,am',rqs,obs) /\
         storage_well_formed_on
           (initial_evaluation_context am.sources am.layouts tx NONE)
           (initial_state am' []) (FST H))) ==>
  ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) (FST H)
Proof
  strip_tac
  >- (fs[frame_resource_starved_def] >>
      metis_tac[guard_nested_frame_outcome, optionTheory.NOT_SOME_NONE]) >>
  drule guard_gas_readings_witness >>
  disch_then (qx_choose_then `gs` (strip_assume_tac o BETA_RULE)) >>
  drule_all guard_nested_result_storage >> simp[]
QED

Triviality guard_trace_storage_induction:
  runtime_bc <> [] /\
  (!e am tx ret r e'.
    vyper_frame_staging fin policy tops runtime_bc am tx e /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD e.contexts)).msgParams.data) ret /\
    vyper_closed_world fin policy tops runtime_bc am tx H e /\
    LENGTH (call_trace e) < 2 ** 64 /\
    2 <= LENGTH e.contexts /\ run_call e = SOME (r,e') /\
    ~MEM tx.target (SND (HD e.contexts)).toDelete /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := (SND (HD e.contexts)).accounts;
                         tStorage := (SND (HD e.contexts)).tStorage|>) (FST H) /\
    (!rq co. MEM (rq,co) (call_trace e) /\
      storage_well_formed_on
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (empty_state with <|accounts := rq.cr_accounts;
                           tStorage := rq.cr_tStorage|>) (FST H) ==>
      storage_well_formed_on
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (empty_state with <|accounts := co.co_accounts;
                           tStorage := co.co_tStorage|>) (FST H)) ==>
    ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := e'.rollback.accounts;
                         tStorage := e'.rollback.tStorage|>) (FST H)) ==>
  !es am tx rq co.
    vyper_frame_staging fin policy tops runtime_bc am tx es /\
    vyper_closed_world fin policy tops runtime_bc am tx H es /\
    MEM (rq,co) (call_trace es) /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H)
Proof
  strip_tac >>
  `WF (inv_image ($< LEX $<)
    (\st:execution_state. contexts_weight 0 st.contexts))` by
    (irule WF_inv_image >> irule WF_LEX >> simp[]) >>
  pop_assum (fn th => ho_match_mp_tac (MATCH_MP WF_INDUCTION_THM th)) >>
  qx_gen_tac `es` >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_state_rel tops runtime_bc am tx es /\ wf_state es` by
    fs[vyper_frame_staging_def, call_state_rel_def, evm_state_ok_def] >>
  mp_tac (Q.INST [`es` |-> `es`, `am` |-> `am`, `tx` |-> `tx`,
    `tops` |-> `tops`, `runtime_bc` |-> `runtime_bc`,
    `rq` |-> `rq`, `co` |-> `co`,
    `regions` |-> `FST (H:(bool # bytes32 # type_value) list # num list)`]
    guard_trace_storage_from_reentries) >>
  reverse impl_tac >- disch_then ACCEPT_TAC >>
  asm_simp_tac bool_ss [] >>
  map_every qx_gen_tac [`s`, `u`, `e`, `r`, `e'`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `u` >>
  `2 <= LENGTH e.contexts` by
    (Cases_on `es.contexts` >> fs[wf_state_def] >> decide_tac) >>
  drule_all guard_reentry_staging >>
  disch_then (qx_choose_then `am_e` (qx_choose_then `tx_e`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `calldata_dispatch _ _ = NONE \/ _` strip_assume_tac
  >- (drule_all guard_undispatched_reentry_rollback >> simp[]) >>
  `(SND (HD e.contexts)).toDelete = e.rollback.toDelete` by
    metis_tac[step_push_saved_to_delete] >>
  `~MEM tx_e.target (SND (HD e.contexts)).toDelete` by
    (qpat_assum `vyper_frame_staging fin policy tops runtime_bc am_e tx_e e`
       (mp_tac o REWRITE_RULE [vyper_frame_staging_def]) >>
     asm_simp_tac bool_ss []) >>
  `($< LEX $<) (contexts_weight 0 e.contexts) (contexts_weight 0 es.contexts)` by
    (drule_all guard_reached_step_weight >> simp[]) >>
  `!st. storage_well_formed_on
          (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE) st (FST H) <=>
        storage_well_formed_on
          (initial_evaluation_context am.sources am.layouts tx NONE) st (FST H)` by
    (gen_tac >> irule storage_well_formed_on_target >> simp[initial_evaluation_context_def]) >>
  qpat_assum `!e am tx ret r e'. _`
    (qspecl_then [`e`, `am_e`, `tx_e`, `ret_e`, `r`, `e'`] mp_tac) >>
  impl_tac
  >- (simp[] >> map_every qx_gen_tac [`rq'`, `co'`] >> strip_tac >>
      qpat_assum `!y. inv_image _ _ y es ==> _` (qspec_then `e` mp_tac) >>
      simp[inv_image_def] >>
      disch_then (qspecl_then [`am_e`, `tx_e`, `rq'`, `co'`] mp_tac) >> simp[]) >>
  simp[]
QED

(* Each reading carries an outcome-prefix simulation and a result proof
   conditional on storage. The re-entry induction closes that condition. *)
Triviality guard_compiler_readings:
  call_guard_gas_link_stmt /\
  vyper_call_staging fin policy tops runtime_bc am tx ret es /\
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  s1_request_prefix tops /\
  run_call es = SOME (r,es') /\ ~frame_resource_starved es r es' ==>
  gas_readings_rel (gas_readings es)
    (\gs.
       (call_storage_ok am tx (MAP SND (call_trace es)) gs ==>
        call_result_rel_at gs tops am tx es r es') /\
       !res am' rqs obs pre rq co sfx.
         call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
           (res,am',rqs,obs) /\
         obs = pre ++ StorageOutcome rq co :: sfx /\
         valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
           (initial_state am []) H pre ==>
         (co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage) \/
         ?rq'. MEM (rq',co) (call_trace es) /\ request_agree H tx.target rq rq')
Proof
  strip_tac >>
  qpat_assum `call_guard_gas_link_stmt`
    (qspecl_then [`fin`, `policy`, `tops`, `runtime_bc`, `am`,
      `tx`, `ret`, `es`, `r`, `es'`] mp_tac o
      REWRITE_RULE [call_guard_gas_link_stmt_def]) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (fn bridge => match_mp_tac (MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_readings_rel_mono) bridge)) >>
  qx_gen_tac `gs` >> BETA_TAC >>
  disch_then (qx_choosel_then
    [`rpolicy`, `unit`, `out`, `prog`, `prog'`, `cplan`, `fmp`, `vs`, `marks`, `tail`]
    (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `vs0 = opt_entry_state_own prog prog' cplan es` >>
  qabbrev_tac `txp = tx with code := vs0.vs_code` >>
  `txp.target = tx.target` by simp[Abbr `txp`] >>
  qpat_assum `vyper_call_staging _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vyper_call_staging_def]) >>
  `external_return_type tops tx.function_name = ret` by
    (qpat_assum `dispatched_vyper_call _ _ _ _`
       (mp_tac o REWRITE_RULE [dispatched_vyper_call_def]) >>
     strip_tac >> simp[external_return_type_def]) >>
  qpat_assum `vyper_frame_staging _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vyper_frame_staging_def]) >>
  qpat_x_assum `?deploy_bc. compile_vyper _ _ _ = _`
    (qx_choose_then `deploy_bc` assume_tac) >>
  `call_state_rel tops (assemble prog') am tx es` by metis_tac[] >>
  `txp = tx` by
    metis_tac[Abbr `txp`, Abbr `vs0`, opt_entry_own_txp_identity] >>
  conj_tac
  >- (strip_tac >>
      qspecl_then [`fin`, `policy`, `tops`, `deploy_bc`,
        `runtime_bc`, `rpolicy`, `unit`, `out`, `prog`, `prog'`,
        `cplan`, `am`, `tx`, `txp`, `ret`, `es`, `vs0`, `fmp`,
        `vs`, `marks`] mp_tac vyper_call_correct_at_marks_own >>
      impl_tac
      >- (asm_simp_tac bool_ss [Abbr `vs0`, Abbr `txp`] >>
          metis_tac[]) >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  map_every qx_gen_tac [`res`, `am'`, `rqs`, `obs`, `pre`, `rq`,
    `co`, `sfx`] >> strip_tac >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    (drule raw_variant_outcomes >>
     simp[Abbr `vs0`, opt_entry_state_own_def, entry_venom_state_frame_fields]) >>
  `~source_exempt tops (res,am',rqs)` by
    (drule call_external_trace_result >> strip_tac >>
     fs[vyper_closed_world_def] >>
     qpat_assum `call_external _ gs am tx = _` (fn source_result =>
       qpat_assum `!gobs. ~source_exempt _ (call_external _ _ _ _)`
         (qspec_then `gs` (ACCEPT_TAC o REWRITE_RULE [source_result])))) >>
  qpat_assum `!tail' res am' rqs obs obs_pre rq outcome sfx H. _`
    (qspecl_then [`tail`, `res`, `am'`, `rqs`, `obs`, `pre`,
      `rq`, `co`, `sfx`, `H`] mp_tac) >>
  impl_tac
  >- (asm_simp_tac bool_ss [Abbr `vs0`, Abbr `txp`] >> metis_tac[]) >>
  strip_tac >> Cases_on `computed_precompile rq` >- gvs[] >>
  qpat_x_assum `~computed_precompile rq ==> _` (strip_assume_tac o
    REWRITE_RULE [ASSUME ``~computed_precompile rq``]) >>
  qabbrev_tac `k = recorded_outcomes_count pre` >>
  qabbrev_tac `D = cx_dead H
    (initial_evaluation_context am.sources am.layouts txp NONE)` >>
  `k < LENGTH (call_requests es) /\
   request_agree_except D (EL k s'.vs_requests) (EL k (call_requests es)) /\
   s.vs_outcomes <> [] /\
   MEM (EL k (call_requests es), HD s.vs_outcomes) (call_trace es)` by
    (qspecl_then [`fin`, `tops`, `am`, `tx`, `rpolicy`, `unit`,
      `out`, `prog`, `cplan`, `prog'`, `es`, `r`, `es'`, `vs0`, `D`,
      `k`, `vs`, `fn`, `inst`, `s`, `fuel`, `s'`, `fn'`,
      `inst'`, `t`, `fuel'`, `t'`] mp_tac codegen_request_cut_outcome >>
     asm_simp_tac bool_ss [Abbr `k`, Abbr `D`, Abbr `vs0`, Abbr `txp`] >>
     metis_tac[]) >>
  disj2_tac >> qexists_tac `EL k (call_requests es)` >>
  conj_tac >- fs[] >>
  `D = external_call_dead H tx (res,am',rqs)` by
    simp[Abbr `D`, cx_dead_def, external_call_dead_def, initial_evaluation_context_def] >>
  `request_agree H tx.target rq (EL k s'.vs_requests)` by fs[Abbr `k`] >>
  metis_tac[request_agree_dead_trans]
QED

(* Supply the single-frame proof whenever a child dispatches. The trace
   induction supplies storage preservation for that child's own calls. *)
Theorem guard_closed_world_readings:
  call_guard_gas_link_stmt /\
  s1_request_prefix tops /\
  vyper_call_staging fin policy tops runtime_bc am tx ret es /\
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  run_call es = SOME (r,es') /\ ~frame_resource_starved es r es' ==>
  gas_readings_rel (gas_readings es)
    (\gs. call_storage_ok am tx (MAP SND (call_trace es)) gs /\
          call_result_rel_at gs tops am tx es r es')
Proof
  strip_tac >>
  `vyper_frame_staging fin policy tops runtime_bc am tx es` by
    metis_tac[vyper_call_staging_def] >>
  `runtime_bc <> []` by (drule guard_frame_runtime_nonempty >> simp[]) >>
  `!rq co.
    MEM (rq,co) (call_trace es) /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H)` by
    (mp_tac guard_trace_storage_induction >>
     asm_simp_tac bool_ss [] >>
     impl_tac
     >- (map_every qx_gen_tac [`e`, `am_e`, `tx_e`, `ret_e`, `r_e`, `e'`] >>
         strip_tac >>
         `~MEM tx_e.target e.rollback.toDelete` by fs[vyper_frame_staging_def] >>
         `~MEM tx_e.target e'.rollback.toDelete` by
           metis_tac[guard_staged_run_no_target_deletion] >>
         irule guard_nested_storage_from_readings >>
         asm_simp_tac bool_ss [] >>
         qexistsl_tac [`fin`, `policy`, `runtime_bc`, `tops`] >>
         asm_simp_tac bool_ss [] >>
         Cases_on `frame_resource_starved e r_e e'` >> simp[] >>
         `vyper_call_staging fin policy tops runtime_bc am_e tx_e ret_e e` by
           fs[vyper_call_staging_def] >>
         mp_tac (Q.INST [`es` |-> `e`, `am` |-> `am_e`, `tx` |-> `tx_e`,
           `ret` |-> `ret_e`, `r` |-> `r_e`, `es'` |-> `e'`] guard_compiler_readings) >>
         impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
         mp_tac (Q.INST [`es` |-> `e`, `am` |-> `am_e`, `tx` |-> `tx_e`,
           `r` |-> `r_e`, `es'` |-> `e'`] guard_close_storage_readings) >>
         impl_tac >- (asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
         disch_then (fn bridge => match_mp_tac (MATCH_MP
           (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_readings_rel_mono) bridge)) >>
         BETA_TAC >> simp[]) >>
     disch_then (qspecl_then [`es`, `am`, `tx`] mp_tac) >> simp[]) >>
  drule_all guard_compiler_readings >> strip_tac >>
  mp_tac guard_close_storage_readings >>
  impl_tac >- (asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  disch_then (fn bridge => match_mp_tac (MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_readings_rel_mono) bridge)) >>
  BETA_TAC >> simp[]
QED

Theorem call_guard_gas_link:
  call_guard_gas_link_stmt
Proof
  rewrite_tac[call_guard_gas_link_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  `fin IN accepted_finalizers /\
   (?deploy_bc. compile_vyper fin policy tops = SOME (deploy_bc,runtime_bc)) /\
   supported_program tops /\ source_typing_ok tops am tx /\
   call_state_rel tops runtime_bc am tx es` by
    fs[vyper_call_staging_def, vyper_frame_staging_def] >>
  pop_assum strip_assume_tac >>
  drule_all guard_runtime_phases >>
  disch_then (qx_choosel_then
    [`rpolicy`, `unit`, `out`, `prog`, `prog'`, `cplan`] strip_assume_tac) >>
  drule_all_then strip_assume_tac call_source_focus_setup >>
  rename1 `lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` >>
  qabbrev_tac `vs0 = opt_entry_state_own prog prog' cplan es` >>
  qabbrev_tac `txp = tx with code := vs0.vs_code` >>
  qabbrev_tac `fmp = (n2w (MAX cplan.cp_initial_fmp
    (unit_alloca_budget unit.cu_context +
     32 * ctx_dload_count unit.cu_context)) : bytes32)` >>
  `vs0 = opt_entry_state_own prog prog' cplan es /\ txp = tx with code := vs0.vs_code` by
    simp[Abbr `vs0`, Abbr `txp`] >>
  pop_assum strip_assume_tac >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `cplan`, `prog`, `prog'`,
               `es`, `fmp`] mp_tac raw_fmp_choice_own >>
  impl_tac >- simp[Abbr `fmp`] >>
  qpat_assum `vs0 = opt_entry_state_own prog prog' cplan es`
    (fn eq => disch_then (strip_assume_tac o REWRITE_RULE [GSYM eq])) >>
  `call_state_rel tops (assemble prog') am tx es /\
   vyper_call_staging fin policy tops (assemble prog') am tx ret es` by fs[] >>
  pop_assum strip_assume_tac >>
  `assemble prog' <> []` by
    (qpat_assum `vyper_call_staging _ _ _ (assemble prog') _ _ _ _`
       (ACCEPT_TAC o MATCH_MP guard_frame_runtime_nonempty o CONJUNCT1 o
        REWRITE_RULE [vyper_call_staging_def])) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_entry_asm_rels_own >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `vs0 = opt_entry_state_own _ _ _ _`
    (fn eq => disch_then (strip_assume_tac o REWRITE_RULE [GSYM eq])) >>
  `code_layout_valid vs0` by metis_tac[opt_entry_code_layout_valid_own] >>
  `o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp` by
    simp[Abbr `vs0`, opt_entry_state_own_def, entry_venom_state_def,
         o1_initial_state_ok_def, init_venom_state_def] >>
  `initial_venom_state_rel tops am txp vs0` by
    metis_tac[opt_entry_initial_venom_state_rel_own] >>
  `source_typing_ok tops am txp` by
    metis_tac[opt_entry_own_txp_identity] >>
  `LENGTH (call_trace es) < 2 ** 64` by fs[vyper_call_staging_def] >>
  drule_all guard_source_marks >>
  disch_then (qx_choose_then `shadow_ctx` assume_tac) >>
  qpat_assum `!vs. raw_variant fmp vs vs0 ==> _` (fn th =>
    let
      val (state, body) = dest_forall (concl th)
      val (marks, certificate) = dest_exists (snd (dest_imp body))
      val prefix = mk_abs (state, mk_abs (marks, snd (dest_conj certificate)))
    in
      mp_tac (CONV_RULE (DEPTH_CONV BETA_CONV)
        (INST [mk_var ("prefix_ok", type_of prefix) |-> prefix]
          (Q.INST [`tx` |-> `txp`] call_marked_focus_family)))
    end) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> metis_tac[]) >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  `fn_entry_label func = SOME "__entry"` by
    (qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (mp_tac o REWRITE_RULE [source_unit_execution_correct_with_def] o
        CONJUNCT1 o Q.SPEC `[]`) >>
     disch_then (qx_choosel_then [`cf`, `shadow_cf`] strip_assume_tac) >>
     `cf = func` by fs[] >> fs[]) >>
  `fin = asm_opt_finalizer ==>
    label_flow_own_ok unit.cu_context /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "code_end") inst.inst_operands) /\
    EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                      ds.ds_items) unit.cu_data_segment /\
    ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                MEM inst (fn_insts fn) /\
                MEM (Label "runtime_begin") inst.inst_operands) ==>
     EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2` by
    (disch_tac >>
     mp_tac (Q.SPECL [`tops`, `rpolicy`, `unit`] lower_vyper_runtime_unit_sym_src_ok_own) >>
     impl_tac >- asm_rewrite_tac[] >> strip_tac >>
     asm_rewrite_tac[] >> metis_tac[data_section_length_bound]) >>
  mp_tac (Q.SPECL [`rpolicy`, `unit`, `out`, `"__entry"`]
    (Q.GENL [`rp`, `unit`, `out`, `nm`] focus_packet_pipeline_stages)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`pre`, `supply`, `supply'`, `stage`] strip_assume_tac) >>
  Q.SPECL_THEN
    [`rpolicy`, `unit`, `out`, `vs0`, `cplan`, `prog`, `fin`, `prog'`, `es`,
     `"__entry"`, `func`, `"__entry"`, `fmp`, `markf`, `0`,
     `\key. key IN gas_explicit_sites unit.cu_context shadow_ctx`,
     `r`, `es'`, `pre`, `supply`, `supply'`, `stage`] mp_tac
    (Q.GENL
      [`rpolicy`, `unit`, `out`, `vs0`, `cpl`, `prog`, `fin`, `prog'`, `es0`,
       `nm`, `entryfn`, `lbl`, `fmp`, `markf`, `lo`, `project`, `result`, `final`,
       `pre`, `t`, `t'`, `stage`]
      focus_finalizer_selected_request_replay_own) >>
  impl_tac
  >- (BETA_TAC >> asm_rewrite_tac[asm_frame_rel_tail_nil] >> gen_tac >>
      qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
        (qx_choosel_then [`D`, `fuel`, `extra`] strip_assume_tac o
         CONJUNCT2 o CONJUNCT2 o Q.SPEC `gs`) >>
      qexistsl_tac [`D`, `fuel`, `extra`] >>
      qpat_x_assum `vs0 = opt_entry_state_own _ _ _ _` SUBST_ALL_TAC >>
      pure_rewrite_tac[venom_state_fupdcanon] >>
      qpat_assum `MAP _ (gas_events_blocks _ _ _ _) = _`
        (fn th => asm_rewrite_tac [REWRITE_RULE [venom_state_fupdcanon] th])) >>
  disch_then (qx_choosel_then [`raw_slots`, `sites`, `unused`] strip_assume_tac) >>
  rewrite_tac[gas_readings_rel_def] >>
  Q.ISPECL_THEN
    [`sites`, `\key. key IN gas_explicit_sites unit.cu_context shadow_ctx`,
     `raw_slots`, `unused`, `gas_readings es`, `markf`]
    (match_mp_tac o BETA_RULE) gas_mask_projection_padded >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `raw` >> strip_tac >>
  qpat_x_assum `!raw. LIST_REL _ raw_slots raw ==> _` (qspec_then `raw` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `suffix` >> BETA_TAC >>
  qabbrev_tac `vs = vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `marks = markf (raw ++ [0w])` >>
  `raw_variant fmp vs vs0` by
    (qunabbrev_tac `vs` >>
     simp[NoAsms, o1PassContractTheory.raw_variant_def,
          o1PassContractTheory.gas_variant_def, venom_state_component_equality]) >>
  qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
    (mp_tac o Q.SPEC `raw ++ [0w]`) >>
  qpat_assum `Abbrev (marks = _)` (fn th =>
    qpat_assum `Abbrev (vs = _)` (fn st =>
      rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th),
                   GSYM (REWRITE_RULE [markerTheory.Abbrev_def] st)])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (K all_tac))) >>
  `source_unit_execution_correct_at marks tops ret am txp unit vs` by
    (rewrite_tac[source_unit_execution_correct_at_def] >>
     qexists_tac `shadow_ctx` >> first_assum ACCEPT_TAC) >>
  `!H:(bool # bytes32 # type_value) list # num list.
     dead_wf (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))` by
    (gen_tac >> simp[NoAsms, cx_dead_def, initial_evaluation_context_def] >>
     MATCH_ACCEPT_TAC
       (SIMP_RULE (srw_ss()) [external_call_dead_def]
         (Q.INST [`src` |-> `(INL NoneV, am, [])`] external_call_dead_wf))) >>
  qexistsl_tac [`rpolicy`, `unit`, `out`, `prog`, `prog'`, `cplan`,
                `fmp`, `vs`, `marks`, `suffix`] >>
  conj_tac >- simp[Abbr `vs`] >>
  `tx.target = txp.target` by simp[Abbr `txp`] >>
  qpat_x_assum `vs0 = opt_entry_state_own _ _ _ _` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
  qpat_x_assum `txp = _` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      drule_all call_focus_callback_inputs >> strip_tac >>
      qpat_assum `!D. (?fr. terminates _) /\ _ ==> _`
        (qspec_then `cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE)` mp_tac) >>
      qpat_assum `Abbrev (vs = _)` (fn eq =>
        rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
      impl_tac
      >- (conj_tac
          >- (qexists_tac `fr` >> first_assum ACCEPT_TAC) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          disch_tac >>
          `vs.vs_code = vs0.vs_code /\ vs.vs_data_section = vs0.vs_data_section` by
            simp[Abbr `vs`] >>
          qpat_assum `vs.vs_code = _` (fn code =>
            qpat_assum `vs.vs_data_section = _` (fn data =>
              qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ vs`
                (ACCEPT_TAC o REWRITE_RULE [code, data])))) >>
      disch_then (mp_tac o CONJUNCT2) >> asm_rewrite_tac[]) >>
  match_mp_tac guard_selected_request_replay >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!D k vs fn inst s fuel s'. _` (mp_tac o Q.SPECL
    [`cx_dead (H:(bool # bytes32 # type_value) list # num list)
        (initial_evaluation_context am.sources am.layouts txp NONE)`,
     `k`, `vs`, `fn`, `inst`, `s`, `fuel`, `s'`]) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- simp[Abbr `vs`] >>
      conj_tac
      >- (qpat_assum `!H. dead_wf (cx_dead H _)`
            (qspec_then `(H:(bool # bytes32 # type_value) list # num list)` ACCEPT_TAC)) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

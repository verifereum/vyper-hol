(* Closed-world storage invariants for a reentered frame. *)
Theory e2eOutcomesGuard
Ancestors
  e2eRequestCutDefs e2eDefs vfmAccountFrame vyperStorageFootprint
  vyperInterpreter vyperState vyperStorageBackend vfmState vfmContext
  callTraceFrameProvenance callTraceFrame callTrace guardReentryCode guardReentryAccounts
  guardPushProjections immutableSectionRel vfmExecution vfmExecutionProp
  e2eCorrectness e2eComposition frameOutcome guardTerminalBackend guardSourceAlignment
  vyperCallFiniteStorageSupport
  vfmDecreasesGas relation pair arithmetic list

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
     ?ret_e. vyper_entry_call tops tx_e
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
    vyper_entry_call tops tx
      (buffer_to_list (FST (HD e.contexts)).msgParams.data) ret /\
    vyper_closed_world fin policy tops runtime_bc am tx H e /\
    LENGTH (call_trace e) < 2 ** 64 /\
    2 <= LENGTH e.contexts /\ run_call e = SOME (r,e') /\
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

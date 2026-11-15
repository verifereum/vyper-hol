(*
 * Closed-world storage guard on callee outcomes, short of the call theorem.
 *
 * Shared premises are defined in e2eOutcomesDefs. At the S1 request-prefix
 * companion's gas marking, closed_world_outcomes_guard proves the guard
 * call_outcomes_storage_ok follows from source_storage_ok, given the
 * producer's conclusion for every re-entry.  e2eOutcomesProducer adds the
 * induction on call depth and the call theorem.
 *)
Theory e2eOutcomesGuard
Ancestors
  e2eOutcomesDefs e2eDefs sourceUnitExecution vyperLoweringCorrect gasSummary compileVyper loweringShapeProps
  supportedProgram callTrace frameOutcome extCallOracle vyperStorageFootprint
  vyperRuntimeAccounts vyperInterpreter venomExecSemantics vyperRequestTrace
  vfmAccountFrame vfmExecution callTraceFrame unitTransformDefs ptrDiscipline
  unitMemInv lowerDloadDefs vyperCallStorageFootprint e2eProducers e2eEntry o1PipelineCorrect o1PassContract o1RequestRuns
  o1PipelineRequests e2eComposition loweringShapeSource immutableCodeLayout staticLayoutDefs
  guardReentryAccounts guardReentryCode guardPushProjections guardTerminalBackend e2eCallAtMarks
  guardSourceAlignment
  callTraceFrameProvenance vfmDecreasesGas relation pair arithmetic list
  vfmAccountDeletion vfmExecutionProp vfmState vyperStorageBackend immutableSectionRel
  guardRequestAlignment loweringMemCorrect guardStorageTransport
  e2eCorrectness e2eDeployCorrectness


(* Phase and marking witnesses are chosen before the storage guard. *)
Theorem closed_world_guard_setup[local]:
  vyper_call_staging policy tops runtime_bc am tx ret es /\
  s1_request_prefix tops ==>
  ?rpolicy unit out prog cp vs marks.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    gas_variant vs (entry_venom_state prog cp es) /\
    (!D. dead_wf D ==>
      raw_unit_memory_ok unit.cu_context vs /\
      ptr_discipline 0 unit.cu_context vs /\
      taint_within D
        unit.cu_context vs /\
      mem_inv dload_offset_ok unit.cu_context vs /\
      mem_inv dload_headroom_ok unit.cu_context vs ==>
      ctx_sim D
        unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
      ctx_abort_rq D
        unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
      o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    !tail res am' rqs obs obs_pre rq outcome sfx H.
      call_external_trace (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) /\
      ~source_exempt tops (res,am',rqs) /\
      obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
      valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am []) H obs_pre ==>
      raw_unit_memory_ok unit.cu_context vs /\
      ptr_discipline 0 unit.cu_context vs /\
      taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
        unit.cu_context vs /\
      mem_inv dload_offset_ok unit.cu_context vs /\
      ?fuel ss.
        (run_context fuel unit.cu_context vs = Halt ss \/
         ?a. run_context fuel unit.cu_context vs = Abort a ss) /\
        (computed_precompile rq ==>
          outcome.co_accounts = rq.cr_accounts /\ outcome.co_tStorage = rq.cr_tStorage) /\
        (~computed_precompile rq ==>
          recorded_outcomes_count obs_pre < LENGTH rqs /\
          recorded_outcomes_count obs_pre < LENGTH ss.vs_requests /\
          EL (recorded_outcomes_count obs_pre) rqs = rq /\
          request_agree H (initial_evaluation_context am.sources am.layouts tx NONE)
            rq (EL (recorded_outcomes_count obs_pre) ss.vs_requests) /\
          (outcome = failed_outcome rq \/
           recorded_outcomes_count obs_pre < LENGTH vs.vs_outcomes /\
           outcome = EL (recorded_outcomes_count obs_pre) vs.vs_outcomes))
Proof
  simp[vyper_call_staging_def] >> rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  qpat_x_assum `prog = _` kall_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `code_layout_valid (entry_venom_state prog cplan es)` by
    (irule generated_entry_code_layout_shape >> metis_tac[]) >>
  `o1_run_state_ok (entry_venom_state prog cplan es)` by
    (simp[o1_run_state_ok_def, entry_venom_state_o1_initial_state_ok] >>
     gvs[entry_venom_state_fresh, entry_venom_state_def, call_state_rel_def]) >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >> simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >> simp[reserved_intervals_wf_def]) >>
  drule_all (run_venom_pipeline_correct_requests_all_dead |> Q.SPEC `0`) >>
  strip_tac >>
  `initial_venom_state_rel tops am tx vs_in` by
    (irule gas_variant_initial_venom_state_rel >>
     goal_assum $ drule_at Any >>
     irule entry_venom_state_initial_venom_state_rel >> simp[]) >>
  `code_layout_valid vs_in` by
    (irule gas_variant_code_layout_valid >> goal_assum $ drule_at Any >>
     irule generated_entry_code_layout_shape >> metis_tac[]) >>
  `vs_in.vs_outcomes = MAP SND (call_trace es) /\
   vs_in.vs_call_ctx.cc_calldata = buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    (drule gas_variant_outcomes >> drule gas_variant_call_ctx >>
     simp[entry_venom_state_def]) >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
    accounts_runtime_well_typed oc.co_accounts) vs_in.vs_outcomes` by
    (simp[] >> irule call_trace_outcomes_bounded >> fs[call_state_rel_def]) >>
  qpat_x_assum `s1_request_prefix tops` mp_tac >>
  simp[ s1_request_prefix_def] >>
  disch_then (qspecl_then [`rpolicy`, `unit`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `shadow_ctx`
    (qspecl_then [`am`, `tx`, `ret`, `vs_in`] mp_tac)) >>
  impl_tac >- simp[] >> strip_tac >>
  `source_unit_execution_correct_at marks tops ret am tx unit vs_in` by
    (simp[source_unit_execution_correct_at_with] >> metis_tac[]) >>
  qexistsl_tac [`vs_in`, `marks`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!D. dead_wf D ==> _` (qspec_then `D` mp_tac) >> simp[]) >>
  gvs[]
QED

Theorem guard_closed_world_inherit[local]:
  vyper_closed_world policy tops runtime_bc am tx H es /\
  run_call_reaches es e /\ LENGTH es.contexts <= LENGTH e.contexts /\
  am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
  tx_e.target = tx.target /\
  storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (initial_state am_e []) (FST H) /\
  horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
  ~account_empty (lookup_account tx_e.target e.originalAccounts) /\
  EVERY (\p. ~computed_precompile (FST p)) (call_trace e) /\
  (!gobs. ~source_exempt tops
    (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e)) ==>
  vyper_closed_world policy tops runtime_bc am_e tx_e H e
Proof
  simp[vyper_closed_world_def] >> rpt strip_tac >>
  rename1 `step s = (INL u, child)` >>
  `run_call_reaches es s` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[]) >>
  qpat_x_assum `!s child. _`
    (qspecl_then [`s`, `child`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

val guard_frame_storage_pair =
  ``\cx (H : (bool # bytes32 # type_value) list # num list) p.
  ~NULL (FST p).code /\
  storage_well_formed_on cx
    (empty_state with <|accounts := K (FST p); tStorage := K (SND p)|>)
    (FST H)``;

Theorem guard_compiled_trace_storage:
  !es am tx ret rq co.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es /\
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
  `WF (inv_image ($< LEX $<)
    (\st:execution_state. contexts_weight 0 st.contexts))` by
    (irule WF_inv_image >> irule WF_LEX >> simp[]) >>
  pop_assum (fn th => ho_match_mp_tac (MATCH_MP WF_INDUCTION_THM th)) >>
  qx_gen_tac `es` >> strip_tac >> rpt gen_tac >> strip_tac >>
  `wf_state es /\
   (FST (HD es.contexts)).msgParams.callee = tx.target` by
    fs[vyper_call_staging_def, call_state_rel_def] >>
  `runtime_bc <> []` by
    (fs[vyper_call_staging_def] >> drule compile_vyper_runtime_nonempty >> simp[]) >>
  `~NULL (lookup_account tx.target es.rollback.accounts).code` by
    (fs[vyper_call_staging_def, call_state_rel_def, installed_code_rel_def, NULL_EQ] >>
     metis_tac[APPEND_eq_NIL]) >>
  `~account_empty (lookup_account tx.target es.originalAccounts)` by
    fs[vyper_closed_world_def] >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `~NULL (lookup_account tx.target rq.cr_accounts).code` by
    (drule_all call_trace_entry_provenance >> strip_tac >> gvs[] >>
     irule guard_reaches_code_nonempty >> qexists_tac `es` >> simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `^guard_frame_storage_pair cx H
    (lookup_account tx.target rq.cr_accounts, rq.cr_tStorage tx.target)` by
    (BETA_TAC >> fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
      lookup_account_def, Abbr `cx`, initial_evaluation_context_def]) >>
  `^guard_frame_storage_pair cx H
    (lookup_account tx.target co.co_accounts, co.co_tStorage tx.target)`
    suffices_by
      (BETA_TAC >> fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
        lookup_account_def, Abbr `cx`, initial_evaluation_context_def]) >>
  BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  irule (BETA_RULE (Q.INST
    [`P` |-> `^guard_frame_storage_pair cx H`, `a` |-> `tx.target`,
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
        [`obs` |-> `\p. ^guard_frame_storage_pair cx H
          (lookup_account tx.target (FST p), SND p tx.target)`,
         `e` |-> `e`, `e'` |-> `e'`, `r` |-> `r`]
        (INST_TYPE [alpha |-> ``:bool``] run_call_static_observation)) >>
      simp[] >> impl_tac
      >- (drule_all step_push_static_output_not_code >> fs[]) >>
      simp[]) >>
  `run_call_reaches es e` by
    (irule run_call_reaches_step >> qexistsl_tac [`s`, `()`] >> simp[]) >>
  `LENGTH es.contexts <= LENGTH e.contexts` by decide_tac >>
  `?am_e tx_e ret_e.
     am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
     vyper_call_staging policy tops runtime_bc am_e tx_e ret_e e /\
     horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
     EVERY (\p. ~computed_precompile (FST p)) (call_trace e) /\
     !gobs. ~source_exempt tops
       (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e)` by
    (qpat_assum `vyper_closed_world _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[vyper_closed_world_def] >>
     disch_then (mp_tac o last o CONJUNCTS) >>
     disch_then (qspecl_then [`s`, `()`, `e`] mp_tac) >> simp[]) >>
  `tx_e.target = tx.target` by
    (fs[vyper_call_staging_def, call_state_rel_def] >>
     metis_tac[listTheory.HD, pairTheory.FST]) >>
  `account_already_created (lookup_account tx.target es.rollback.accounts)` by
    fs[account_already_created_def] >>
  `~account_empty (lookup_account tx_e.target e.originalAccounts)` by
    (mp_tac (guard_reaches_created_original_nonempty |> Q.INST
      [`es` |-> `es`, `s` |-> `e`, `a` |-> `tx.target`]) >> simp[]) >>
  `!addr. (accounts_after_transfer tx_e am_e.accounts addr).storage =
           (am_e.accounts addr).storage` by
    (gen_tac >> rw[accounts_after_transfer_def, lookup_account_def,
                  update_account_def, combinTheory.APPLY_UPDATE_THM] >>
     rpt IF_CASES_TAC >> simp[]) >>
  `storage_well_formed_on
     (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
     (initial_state am_e []) (FST H)` by
    (fs[vyper_call_staging_def, call_state_rel_def, storage_well_formed_on_def, boolTheory.FORALL_BOOL,
        get_storage_def, initial_state_def, Abbr `cx`, initial_evaluation_context_def,
        lookup_account_def] >> rpt strip_tac >> fs[]) >>
  `vyper_closed_world policy tops runtime_bc am_e tx_e H e` by
    (mp_tac (guard_closed_world_inherit |> Q.INST
       [`am` |-> `am`, `tx` |-> `tx`, `es` |-> `es`]) >>
     impl_tac >- (simp[] >> decide_tac) >> simp[]) >>
  `($< LEX $<) (contexts_weight 0 e.contexts)
     (contexts_weight 0 es.contexts)` by
    (drule_all guard_reached_step_weight >> simp[]) >>
  `!rq' co'. MEM (rq',co') (call_trace e) /\
    storage_well_formed_on
      (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
      (empty_state with <|accounts := rq'.cr_accounts;
                         tStorage := rq'.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
      (empty_state with <|accounts := co'.co_accounts;
                         tStorage := co'.co_tStorage|>) (FST H)` by
    (qpat_assum `!y. inv_image _ _ y es ==> _` (qspec_then `e` mp_tac) >>
     simp[inv_image_def] >>
     disch_then (qspecl_then [`am_e`, `tx_e`, `ret_e`] mp_tac) >> simp[]) >>
  mp_tac (closed_world_guard_setup |> Q.INST
    [`policy` |-> `policy`, `tops` |-> `tops`, `runtime_bc` |-> `runtime_bc`,
     `am` |-> `am_e`, `tx` |-> `tx_e`, `ret` |-> `ret_e`, `es` |-> `e`]) >>
  simp[] >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  `vs.vs_outcomes = MAP SND (call_trace e)` by
    (drule gas_variant_outcomes >> simp[entry_venom_state_def]) >>
  `runtime_bc = assemble prog` by
    (fs[vyper_call_staging_def] >>
     drule compile_vyper_runtime_phases >> strip_tac >> gvs[]) >>
  `initial_venom_state_rel tops am_e tx_e vs` by
    (irule gas_variant_initial_venom_state_rel >> goal_assum $ drule_at Any >>
     irule entry_venom_state_initial_venom_state_rel >> fs[vyper_call_staging_def]) >>
  `mem_inv dload_headroom_ok unit.cu_context vs` by
    (drule_all lower_vyper_runtime_unit_dload_headroom_ok >> simp[]) >>
  `?deploy_bc. compile_vyper (K SOME) policy tops = SOME (deploy_bc,runtime_bc)` by
    fs[vyper_call_staging_def] >>
  mp_tac (Q.SPECL
    [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `am_e`, `tx_e`, `ret_e`, `e`,
     `rpolicy`, `unit`, `out`, `prog`, `cplan`, `vs`, `marks`]
    vyper_call_correct_at_marks) >>
  impl_tac
  >- (fs[vyper_call_staging_def] >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `dead_wf (cx_dead H' (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE))` by
        (Q.ISPECL_THEN [`H'`, `tx_e`] mp_tac
          (Q.GENL [`H`, `tx`] (Q.INST [`src` |-> `(ARB,ARB,ARB)`] external_call_dead_wf)) >>
         simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]) >>
      qpat_assum `!D. dead_wf D ==> _`
        (qspec_then `cx_dead H' (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)` mp_tac) >>
        impl_tac >- simp[] >> impl_tac >- simp[] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        fs[cx_dead_def, initial_evaluation_context_def] >> gvs[]) >>
  strip_tac >> gvs[]
  >- (fs[frame_resource_starved_def, frame_outcome_def] >>
      Cases_on `rest` >> gvs[] >> Cases_on `h` >> gvs[]) >>
  qabbrev_tac `gs = gas_explicit marks vs.vs_gas_readings` >>
  `?res_e am_f rqs_e obs_e.
    call_external_trace (SOME (MAP SND (call_trace e))) gs am_e tx_e =
      (res_e,am_f,rqs_e,obs_e)` by
    (qmatch_goalsub_abbrev_tac `selected = _` >>
     qexistsl_tac [`FST selected`, `FST (SND selected)`,
       `FST (SND (SND selected))`, `SND (SND (SND selected))`] >> simp[]) >>
  `EVERY (\region. MEM region (FST H)) (storage_trace_regions obs_e) /\
   EVERY (\slot. MEM slot (SND H)) (storage_trace_locks obs_e) /\
   storage_roots_fit obs_e` by
    (qpat_x_assum `horizon_covers H am_e tx_e _` mp_tac >>
     simp[horizon_covers_def] >> disch_then (qspec_then `gs` mp_tac) >>
     drule call_external_trace_result >> simp[]) >>
  `~source_exempt tops (res_e,am_f,rqs_e)` by
    (drule call_external_trace_result >> metis_tac[]) >>
  `storage_observations_ok
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE) H obs_e` by
    (mp_tac (aligned_trace_storage_observations |> Q.INST
       [`tops` |-> `tops`, `am` |-> `am_e`, `tx` |-> `tx_e`, `H` |-> `H`,
        `cx` |-> `initial_evaluation_context am_e.sources am_e.layouts tx_e NONE`,
        `os` |-> `MAP SND (call_trace e)`, `gs` |-> `gs`,
        `res` |-> `res_e`, `am'` |-> `am_f`, `rqs` |-> `rqs_e`,
        `obs` |-> `obs_e`, `trace` |-> `call_trace e`]) >>
     impl_tac
     >- (fs[vyper_call_staging_def, vyper_closed_world_def] >>
     reverse conj_tac >- gvs[] >>
     map_every qx_gen_tac [`pre`, `source_rq`, `source_co`, `sfx`] >> strip_tac >>
     qpat_x_assum `!tail res am' rqs obs_pre rq outcome sfx H. _`
       (qspecl_then [`[]`, `res_e`, `am_f`, `rqs_e`,
         `pre`, `source_rq`, `source_co`, `sfx`, `H`] mp_tac) >>
     simp[Abbr `gs`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `?fuel ss. _`
       (qx_choose_then `fuel` (qx_choose_then `ss` (map_every assume_tac o CONJUNCTS))) >>
     Cases_on `computed_precompile source_rq` >- metis_tac[] >>
     Cases_on `source_co = failed_outcome source_rq`
     >- gvs[failed_outcome_def] >>
     qpat_assum `~computed_precompile source_rq` (fn no_pc =>
       qpat_assum `source_co <> failed_outcome source_rq` (fn no_fail =>
         RULE_L_ASSUM_TAC (CONJUNCTS o SIMP_RULE (srw_ss()) [no_pc,no_fail]))) >>
     disj2_tac >>
     `ctx_sim (cx_dead H
        (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE))
        unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan e) /\
      ctx_abort_rq (cx_dead H
        (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE))
        unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan e) /\
      o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cplan e)` by
       (`dead_wf (cx_dead H (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE))` by
          (Q.ISPECL_THEN [`H`, `tx_e`] mp_tac
          (Q.GENL [`H`, `tx`] (Q.INST [`src` |-> `(ARB,ARB,ARB)`] external_call_dead_wf)) >>
           simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]) >>
        qpat_assum `!D. dead_wf D ==> _`
          (qspec_then `cx_dead H (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)` mp_tac) >>
        impl_tac >- simp[] >> impl_tac >- simp[] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        fs[cx_dead_def, initial_evaluation_context_def] >> gvs[]) >>
     `recorded_outcomes_count pre < LENGTH vs.vs_outcomes` by simp[] >>
     qpat_assum `am_e.sources = am.sources` (fn sources_eq =>
       qpat_assum `am_e.layouts = am.layouts` (fn layouts_eq =>
         RULE_ASSUM_TAC (PURE_REWRITE_RULE [sources_eq,layouts_eq]) >>
         drule_all (PURE_REWRITE_RULE [sources_eq,layouts_eq]
           (SPEC_ALL source_compiled_request_alignment |> Q.INST
             [`am` |-> `am_e`, `tx` |-> `tx_e`, `es` |-> `e`, `H` |-> `H`])))) >>
     strip_tac >>
     qexists_tac `EL (recorded_outcomes_count pre) (call_requests e)` >> gvs[]) >>
     simp[]) >>
  `!st. storage_well_formed_on
      (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE) st (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE) st
      (storage_trace_regions obs_e)` by
    (simp[storage_well_formed_on_def] >> rpt strip_tac >>
     qpat_x_assum `!b slot tv. MEM _ (FST H) ==> _` irule >> fs[EVERY_MEM]) >>
  `storage_trace_backends_well_formed
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (storage_trace_regions obs_e) obs_e` by
    (simp[storage_trace_backends_well_formed_def] >>
     irule EVERY_MONOTONIC >>
     qexists_tac `\ob. case ob of StorageBackend acc ts =>
       storage_well_formed_on
         (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
         (empty_state with <|accounts := acc; tStorage := ts|>) (FST H)
       | _ => T` >>
     conj_tac
     >- (Cases >> simp[] >> metis_tac[]) >>
     fs[storage_observations_ok_def, storage_trace_backends_well_formed_def]) >>
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)` by
    fs[vyper_closed_world_def] >>
  `source_storage_ok am_e tx_e (MAP SND (call_trace e)) gs /\
   call_outcomes_storage_ok am_e tx_e (MAP SND (call_trace e)) gs` by
    (drule call_external_trace_result >> strip_tac >>
     simp[source_storage_ok_def, call_outcomes_storage_ok_def,
       storage_trace_horizon_def] >>
     fs[regions_consistent_def, storage_locks_separated_def, EVERY_MEM] >>
     metis_tac[]) >>
  `call_result_rel_at gs tops ret_e am_e tx_e e r e'` by
    (qpat_x_assum `!tail. source_storage_ok _ _ _ _ /\ _ ==> _`
       (qspec_then `[]` mp_tac) >> simp[Abbr `gs`]) >>
  `storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (initial_state am_f []) (FST H)` by
    (`?art_e. check_contract F am_e.layouts tx_e.target [(NONE,tops)] = SOME art_e /\
       checked_contract_runtime_ready art_e [(NONE,tops)] am_e tx_e /\
       machine_well_typed am_e /\ call_tx_well_typed tx_e` by
       (simp[GSYM source_typing_ok_def] >> fs[vyper_call_staging_def]) >>
        mp_tac (checked_call_external_preserves_storage_well_formed_on |> Q.INST
       [`am` |-> `am_e`, `tx` |-> `tx_e`, `mods` |-> `[(NONE,tops)]`,
        `art` |-> `art_e`, `orc` |-> `SOME (MAP SND (call_trace e))`,
        `gobs` |-> `gs`, `res` |-> `res_e`, `am'` |-> `am_f`,
        `rqs` |-> `rqs_e`, `obs` |-> `obs_e`, `H` |-> `H`,
        `cx` |-> `initial_evaluation_context am_e.sources am_e.layouts tx_e NONE`]) >>
     impl_tac >- (fs[vyper_closed_world_def, initial_evaluation_context_def] >> gvs[]) >>
     simp[]) >>
  `~MEM tx_e.target e'.rollback.toDelete` by
    (strip_tac >> drule_all run_call_to_delete >>
     drule_all step_push_saved_to_delete >>
     fs[vyper_call_staging_def, call_state_rel_def] >> gvs[]) >>
  `storage_well_formed_on cx
    (empty_state with <|accounts := e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) (FST H)` by
    (mp_tac (INST_TYPE [alpha |-> ``:num list``] guard_terminal_backend_well_formed |> Q.INST
       [`e` |-> `e`, `e'` |-> `e'`, `tx` |-> `tx_e`, `gs` |-> `gs`,
        `am` |-> `am_e`, `res` |-> `res_e`, `am'` |-> `am_f`,
        `rqs` |-> `rqs_e`, `obs` |-> `obs_e`, `tops` |-> `tops`,
        `ret` |-> `ret_e`, `r` |-> `r`, `H` |-> `H`, `cx` |-> `cx`]) >>
     impl_tac
     >- (fs[Abbr `cx`, initial_evaluation_context_def, storage_well_formed_on_def, boolTheory.FORALL_BOOL,
            get_storage_def, initial_state_def, lookup_account_def] >> gvs[]) >> simp[]) >>
  `?exc out lgs. frame_outcome e r e' exc out lgs` by
    (drule call_external_trace_result >> strip_tac >>
     qpat_x_assum `call_result_rel_at _ _ _ _ _ _ _ _` mp_tac >>
     simp[call_result_rel_at_def, source_storage_trace_def] >>
     Cases_on `res_e`
     >- (simp[call_success_rel_def] >> metis_tac[]) >>
     rename1 `INR exc` >> Cases_on `exc = HaltException`
     >- (gvs[] >> metis_tac[]) >>
     Cases_on `exc` >> simp[exception_outcome_rel_def] >>
     rpt strip_tac >> gvs[source_exempt_def] >> metis_tac[]) >>
  `ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts` by
    (fs[frame_outcome_def] >> Cases_on `rest` >> gvs[] >>
     Cases_on `h` >> gvs[] >>
     qpat_assum `MAP FST _ = MAP FST _`
       (mp_tac o AP_TERM ``LENGTH:context list -> num``) >> simp[] >> decide_tac) >>
  `run_call_reaches e e'` by
    (drule run_call_finite_trace >> strip_tac >>
     mp_tac (Q.SPEC `n` (Q.INST [`es` |-> `e`] run_call_trace_reaches)) >>
     simp[] >> metis_tac[]) >>
  `run_call_reaches es e'` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[] >> decide_tac) >>
  `LENGTH es.contexts <= LENGTH e'.contexts` by decide_tac >>
  `~NULL (lookup_account tx.target e'.rollback.accounts).code` by
    (drule_all guard_reaches_code_nonempty >> simp[] >> decide_tac) >>
  fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def, lookup_account_def,
     Abbr `cx`, initial_evaluation_context_def]
QED

(* The substance of the producer, short of the call theorem.  For the
   lowered unit and the raw-unit entry state vs the compiled run of es starts
   from (up to its gas readings), at the S1 companion's gas marking, the
   storage guard on callee outcomes follows from the guard on the call's own
   storage, given that every re-entry into the contract during the call meets
   the producer's conclusion (the induction hypothesis on call depth that
   closed_world_call_outcomes_ok discharges). *)
Theorem closed_world_outcomes_guard:
  !policy tops runtime_bc am tx ret es H.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es /\
    (!s u e am_e tx_e ret_e.
       run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
       step s = (INL u, e) /\ LENGTH s.contexts < LENGTH e.contexts /\
       (FST (HD e.contexts)).msgParams.callee = tx.target /\
       ~(FST (HD e.contexts)).msgParams.static /\
       am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
       vyper_call_staging policy tops runtime_bc am_e tx_e ret_e e /\
       vyper_closed_world policy tops runtime_bc am_e tx_e H e ==>
       ?r_e e'.
         run_call e = SOME (r_e, e') /\
         (frame_resource_starved e r_e e' \/
          gas_readings_rel (gas_readings e)
            (\gobs.
               source_storage_ok am_e tx_e (MAP SND (call_trace e)) gobs ==>
               call_outcomes_storage_ok am_e tx_e (MAP SND (call_trace e)) gobs /\
               call_result_rel_at gobs tops ret_e am_e tx_e e r_e e') T)) ==>
    ?rpolicy unit out prog cp vs marks.
      resolve_o1_policy policy = SOME rpolicy /\
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      o1_pipeline rpolicy unit = SOME out /\
      codegen_assembly rpolicy out.po_unit = SOME prog /\
      generate_context_plan out.po_unit.cu_context = SOME cp /\
      gas_variant vs (entry_venom_state prog cp es) /\
      (!H'. raw_unit_memory_ok unit.cu_context vs /\
       ptr_discipline 0 unit.cu_context vs /\
       taint_within (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
         unit.cu_context vs /\
       mem_inv dload_offset_ok unit.cu_context vs /\
       mem_inv dload_headroom_ok unit.cu_context vs ==>
       ctx_sim (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
         unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
       ctx_abort_rq (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
         unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
       o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
      source_unit_execution_correct_at marks tops ret am tx unit vs /\
      !tail.
        source_storage_ok am tx (MAP SND (call_trace es))
          (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
        call_outcomes_storage_ok am tx (MAP SND (call_trace es))
          (gas_explicit marks vs.vs_gas_readings ++ tail)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all closed_world_guard_setup >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qexistsl_tac [`rpolicy`, `unit`, `out`, `prog`, `cplan`, `vs`, `marks`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (qx_gen_tac `H'` >> strip_tac >>
      `dead_wf (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))` by
        (Q.ISPECL_THEN [`H'`, `tx`] mp_tac
          (Q.GENL [`H`, `tx`] (Q.INST [`src` |-> `(ARB,ARB,ARB)`] external_call_dead_wf)) >>
         simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]) >>
      qpat_assum `!D. dead_wf D ==> _`
        (qspec_then `cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE)` mp_tac) >>
        impl_tac >- simp[] >> impl_tac >- simp[] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        fs[cx_dead_def, initial_evaluation_context_def] >> gvs[]) >>
  gen_tac >> strip_tac >>
  qabbrev_tac `gs = gas_explicit marks vs.vs_gas_readings ++ tail` >>
  `?res am' rqs obs.
    call_external_trace (SOME vs.vs_outcomes) gs am tx = (res,am',rqs,obs)` by
    metis_tac[pairTheory.pair_CASES] >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    (drule gas_variant_outcomes >> simp[entry_venom_state_def]) >>
  `source_storage_trace am tx (MAP SND (call_trace es)) gs = obs /\
   call_external (SOME vs.vs_outcomes) gs am tx = (res,am',rqs)` by
    (drule call_external_trace_result >> simp[]) >>
  `~source_exempt tops (res,am',rqs)` by
    (fs[vyper_closed_world_def] >> metis_tac[]) >>
  `EVERY (\r. MEM r (FST H)) (storage_trace_regions obs) /\
   EVERY (\l. MEM l (SND H)) (storage_trace_locks obs) /\
   storage_roots_fit obs` by
    (fs[vyper_closed_world_def, horizon_covers_def] >> metis_tac[]) >>
  `regions_consistent (FST H) /\
   storage_locks_separated (FST H) (SND H) /\
   storage_well_formed_on
     (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) (FST H)` by fs[vyper_closed_world_def] >>
  `EVERY (\p. ~computed_precompile (FST p)) (call_trace es)` by
    fs[vyper_closed_world_def] >>
  `source_typing_ok tops am tx /\ supported_program tops /\
   call_state_rel tops (assemble prog) am tx es` by
    (fs[vyper_call_staging_def] >>
     drule compile_vyper_runtime_phases >> strip_tac >> gvs[]) >>
  `initial_venom_state_rel tops am tx vs` by
    (irule gas_variant_initial_venom_state_rel >> goal_assum $ drule_at Any >>
     irule entry_venom_state_initial_venom_state_rel >> simp[]) >>
  `mem_inv dload_headroom_ok unit.cu_context vs` by
    (drule_all lower_vyper_runtime_unit_dload_headroom_ok >> simp[]) >>
  `storage_observations_ok
     (initial_evaluation_context am.sources am.layouts tx NONE) H obs` by
    (mp_tac (SPEC_ALL aligned_trace_storage_observations |> Q.INST
       [`tops` |-> `tops`, `am` |-> `am`, `tx` |-> `tx`,
        `os` |-> `vs.vs_outcomes`, `gs` |-> `gs`, `res` |-> `res`,
        `am'` |-> `am'`, `rqs` |-> `rqs`, `obs` |-> `obs`,
        `H` |-> `H`,
        `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
        `trace` |-> `call_trace es`]) >>
     impl_tac >- (asm_rewrite_tac[] >> reverse conj_tac
     >- (rpt gen_tac >> strip_tac >>
         mp_tac (SPEC_ALL guard_compiled_trace_storage |> Q.INST
           [`es` |-> `es`, `am` |-> `am`, `tx` |-> `tx`,
            `ret` |-> `ret`, `policy` |-> `policy`, `tops` |-> `tops`,
            `runtime_bc` |-> `runtime_bc`, `H` |-> `H`,
            `rq` |-> `rq`, `co` |-> `co`]) >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!tail res am' rqs obs obs_pre rq outcome sfx H. _`
       (qspecl_then [`tail`, `res`, `am'`, `rqs`, `obs`, `pre`, `rq`, `co`, `sfx`, `H`]
          mp_tac) >>
     impl_tac >- fs[Abbr `gs`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `?fuel ss. _`
       (qx_choose_then `fuel` (qx_choose_then `ss` (map_every assume_tac o CONJUNCTS))) >>
     Cases_on `computed_precompile rq`
     >- gvs[] >>
     Cases_on `co = failed_outcome rq`
     >- gvs[failed_outcome_def] >>
     qpat_assum `~computed_precompile rq` (fn no_pc =>
       qpat_assum `co <> failed_outcome rq` (fn no_fail =>
         RULE_L_ASSUM_TAC (CONJUNCTS o SIMP_RULE (srw_ss()) [no_pc,no_fail]))) >>
     `ctx_sim (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
       unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan es) /\
      ctx_abort_rq (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
       unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan es) /\
      o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cplan es)` by
       (`dead_wf (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))` by
          (Q.ISPECL_THEN [`H`, `tx`] mp_tac
          (Q.GENL [`H`, `tx`] (Q.INST [`src` |-> `(ARB,ARB,ARB)`] external_call_dead_wf)) >>
           simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]) >>
        qpat_assum `!D. dead_wf D ==> _`
          (qspec_then `cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)` mp_tac) >>
        impl_tac >- simp[] >> impl_tac >- simp[] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        fs[cx_dead_def, initial_evaluation_context_def] >> gvs[]) >>
     `recorded_outcomes_count pre < LENGTH vs.vs_outcomes` by gvs[] >>
     drule_all source_compiled_request_alignment >> strip_tac >>
     disj2_tac >>
     qexists_tac `EL (recorded_outcomes_count pre) (call_requests es)` >> gvs[]) >> simp[]) >>
  fs[call_outcomes_storage_ok_def, storage_trace_horizon_def] >>
  fs[storage_observations_ok_def, storage_trace_backends_well_formed_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >>
  Cases_on `observation` >> simp[] >>
  fs[storage_well_formed_on_def, EVERY_MEM] >> metis_tac[]
QED

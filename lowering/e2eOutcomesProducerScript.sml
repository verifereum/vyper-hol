(*
 * Closed-world producer of the storage guard on callee outcomes.
 *
 * call_result_rel guards call_result_rel_at by call_outcomes_storage_ok: the
 * contract's storage backends the source run adopts from call outcomes are
 * well formed on the run's own horizon.  When every re-entry into the
 * contract during the call is itself a call to the same compiled contract,
 * on one storage horizon H shared with the caller, the guard holds and
 * closed_world_call_outcomes_ok concludes the call theorem without it.
 *
 * The S1 request-prefix companion (while the trace up to the k-th recorded
 * outcome is a valid horizon, the lowered unit is memory safe, terminates,
 * and its k-th request agrees with the source's, whose outcome is the k-th
 * callee outcome) is carried as the premise s1_request_prefix until the
 * lowering proof provides it.
 *
 * TOP-LEVEL: closed_world_call_outcomes_ok
 *)
Theory e2eOutcomesProducer
Ancestors
  e2eOutcomesDefs e2eOutcomesGuard e2eCallAtMarks guardSourceAlignment guardRequestAlignment
  e2eDefs e2eComposition e2eProducers e2eEntry vyperInterpreter
  vyperStorageFootprint extCallOracle loweringMemCorrect vyperLoweringCorrect
  e2eCorrectness
  list


(* ADMITTED (argon, 2026-11-13): the per-filling gas link.  The guard setup
   proves these facts for the one raw entry state the O1 pipeline theorem
   picks; this admits that every source-compatible gas filling is read by
   some gas variant of the entry state with the same facts.  Removal is
   tracked separately (call-side twin of deploy_pipeline_gas_link). *)
Theorem call_guard_gas_link:
  !policy tops runtime_bc am tx ret es r es'.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    run_call es = SOME (r, es') /\
    ~frame_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. source_storage_ok am tx (MAP SND (call_trace es)) gs ==>
         ?rpolicy unit out prog cp vs marks tail.
           gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
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
           !tail' res am' rqs obs obs_pre rq outcome sfx H.
             call_external_trace (SOME vs.vs_outcomes)
               (gas_explicit marks vs.vs_gas_readings ++ tail') am tx = (res,am',rqs,obs) /\
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
                  outcome = EL (recorded_outcomes_count obs_pre) vs.vs_outcomes)))
      T
Proof
  cheat
QED

Triviality gas_readings_rel_T_mono:
  gas_readings_rel rs P T /\ (!g. P g ==> Q g) ==> gas_readings_rel rs Q T
Proof
  simp[gas_readings_rel_def] >> metis_tac[]
QED

Theorem closed_world_call_outcomes_ok:
  !policy tops runtime_bc am tx ret es H.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gobs.
            source_storage_ok am tx (MAP SND (call_trace es)) gobs ==>
            call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gobs /\
            call_result_rel_at gobs tops ret am tx es r es') T)
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `am`, `tx`, `ret`, `es`, `r`, `es'`]
    mp_tac (INST_TYPE [alpha |-> ``:256``] call_guard_gas_link) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_readings_rel _ _ T` (fn bridge =>
    match_mp_tac (MATCH_MP
      (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_readings_rel_T_mono) bridge)) >>
  gen_tac >> BETA_TAC >> ntac 2 strip_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  `?deploy_bc. compile_vyper (K SOME) policy tops = SOME (deploy_bc,runtime_bc)` by
    fs[vyper_call_staging_def] >>
  `runtime_bc = assemble prog` by
    (drule compile_vyper_runtime_phases >> strip_tac >> gvs[]) >>
  `initial_venom_state_rel tops am tx vs` by
    (irule gas_variant_initial_venom_state_rel >>
     goal_assum $ drule_at Any >>
     irule entry_venom_state_initial_venom_state_rel >>
     fs[vyper_call_staging_def]) >>
  drule_all lower_vyper_runtime_unit_dload_headroom_ok >> strip_tac >>
  mp_tac (Q.SPECL
    [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `am`, `tx`, `ret`, `es`,
     `rpolicy`, `unit`, `out`, `prog`, `cplan`, `vs`, `marks`]
    vyper_call_correct_at_marks) >>
  impl_tac
  >- (fs[vyper_call_staging_def] >> rpt strip_tac >>
      qpat_assum `!H'. _ ==> ctx_sim _ _ _ _ _ /\ ctx_abort_rq _ _ _ _ _ /\ _`
        (qspec_then `H'` mp_tac) >> simp[]) >>
  disch_then (qx_choosel_then [`r1`, `es1`]
    (map_every assume_tac o CONJUNCTS)) >>
  `r1 = r /\ es1 = es'` by fs[] >>
  qpat_x_assum `r1 = r` SUBST_ALL_TAC >> qpat_x_assum `es1 = es'` SUBST_ALL_TAC >>
  qpat_x_assum `_ \/ _` mp_tac >> simp[] >> strip_tac >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    (drule gas_variant_outcomes >> simp[entry_venom_state_def]) >>
  `?res am_f rqs obs.
    call_external_trace (SOME (MAP SND (call_trace es))) g am tx =
      (res,am_f,rqs,obs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  `EVERY (\region. MEM region (FST H)) (storage_trace_regions obs) /\
   EVERY (\slot. MEM slot (SND H)) (storage_trace_locks obs) /\
   storage_roots_fit obs` by
    (`horizon_covers H am tx (MAP SND (call_trace es))` by fs[vyper_closed_world_def] >>
     pop_assum mp_tac >>
     simp[horizon_covers_def] >> disch_then (qspec_then `g` mp_tac) >>
     drule call_external_trace_result >> simp[]) >>
  `~source_exempt tops (res,am_f,rqs)` by
    (drule call_external_trace_result >> fs[vyper_closed_world_def] >> metis_tac[]) >>
  `regions_consistent (FST H) /\
   storage_locks_separated (FST H) (SND H) /\
   storage_well_formed_on
     (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) (FST H)` by fs[vyper_closed_world_def] >>
  `source_typing_ok tops am tx /\ supported_program tops /\
   call_state_rel tops (assemble prog) am tx es` by fs[vyper_call_staging_def] >>
  `EVERY (\p. ~computed_precompile (FST p)) (call_trace es)` by
    fs[vyper_closed_world_def] >>
  `storage_observations_ok
    (initial_evaluation_context am.sources am.layouts tx NONE) H obs` by
    (mp_tac (SPEC_ALL aligned_trace_storage_observations |> Q.INST
       [`tops` |-> `tops`, `am` |-> `am`, `tx` |-> `tx`, `H` |-> `H`,
        `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
        `os` |-> `MAP SND (call_trace es)`, `gs` |-> `g`,
        `res` |-> `res`, `am'` |-> `am_f`, `rqs` |-> `rqs`,
        `obs` |-> `obs`, `trace` |-> `call_trace es`]) >>
     impl_tac
     >- (asm_rewrite_tac[] >>
         conj_tac
         >- (map_every qx_gen_tac [`pre`, `source_rq`, `source_co`, `sfx`] >> strip_tac >>
             qpat_assum `!tail' res am' rqs obs_pre rq outcome sfx H. _`
               (qspecl_then [`tail`, `res`, `am_f`, `rqs`,
                 `pre`, `source_rq`, `source_co`, `sfx`, `H`] mp_tac) >>
             impl_tac >- gvs[] >>
             disch_then (map_every assume_tac o CONJUNCTS) >>
             qpat_x_assum `?fuel ss. _`
               (qx_choose_then `fuel` (qx_choose_then `ss`
                 (map_every assume_tac o CONJUNCTS))) >>
             Cases_on `computed_precompile source_rq` >- metis_tac[] >>
             Cases_on `source_co = failed_outcome source_rq`
             >- gvs[failed_outcome_def] >>
             qpat_assum `~computed_precompile source_rq` (fn no_pc =>
               qpat_assum `source_co <> failed_outcome source_rq` (fn no_fail =>
                 RULE_L_ASSUM_TAC
                   (CONJUNCTS o SIMP_RULE (srw_ss()) [no_pc,no_fail]))) >>
             disj2_tac >>
             `ctx_sim (cx_dead H
                (initial_evaluation_context am.sources am.layouts tx NONE))
                unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan es) /\
              ctx_abort_rq (cx_dead H
                (initial_evaluation_context am.sources am.layouts tx NONE))
                unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan es) /\
              o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cplan es)` by
               (qpat_assum `!H'. _ ==> ctx_sim _ _ _ _ _ /\ ctx_abort_rq _ _ _ _ _ /\ _`
                  (qspec_then `H` mp_tac) >> simp[]) >>
             `recorded_outcomes_count pre < LENGTH vs.vs_outcomes` by gvs[] >>
             drule_all source_compiled_request_alignment >> strip_tac >>
             qexists_tac `EL (recorded_outcomes_count pre) (call_requests es)` >> gvs[]) >>
         rpt strip_tac >>
         mp_tac (SPEC_ALL guard_compiled_trace_storage |> Q.INST
           [`es` |-> `es`, `am` |-> `am`, `tx` |-> `tx`,
            `ret` |-> `ret`, `policy` |-> `policy`, `tops` |-> `tops`,
            `runtime_bc` |-> `runtime_bc`, `H` |-> `H`,
            `rq` |-> `rq`, `co` |-> `co`]) >> simp[]) >>
     simp[]) >>
  `!st. storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE) st (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE) st
      (storage_trace_regions obs)` by
    (simp[storage_well_formed_on_def] >> rpt strip_tac >>
     qpat_x_assum `!b slot tv. MEM _ (FST H) ==> _` irule >> fs[EVERY_MEM]) >>
  `storage_trace_backends_well_formed
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (storage_trace_regions obs) obs` by
    (simp[storage_trace_backends_well_formed_def] >>
     irule EVERY_MONOTONIC >>
     qexists_tac `\ob. case ob of StorageBackend acc ts =>
       storage_well_formed_on
         (initial_evaluation_context am.sources am.layouts tx NONE)
         (empty_state with <|accounts := acc; tStorage := ts|>) (FST H)
       | _ => T` >>
     conj_tac
     >- (Cases >> simp[] >> metis_tac[]) >>
     fs[storage_observations_ok_def, storage_trace_backends_well_formed_def]) >>
  `call_outcomes_storage_ok am tx (MAP SND (call_trace es)) g` by
    (drule call_external_trace_result >> strip_tac >>
     simp[call_outcomes_storage_ok_def, storage_trace_horizon_def]) >>
  simp[] >>
  qpat_x_assum `!tail. _ ==> call_result_rel_at _ tops ret am tx es r es'`
    (qspec_then `tail` mp_tac) >> gvs[]
QED

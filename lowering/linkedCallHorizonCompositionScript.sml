(* Compose linked source, O1 and frame results at a fixed gas observation. *)
Theory linkedCallHorizonComposition
Ancestors
  sourceUnitExecutionMods e2eModsDefs e2eComposition e2eDefs
  sourceExemptMods vyperLoweringCorrect unitTransformDefs ptrDiscipline
  loweringStateRelDefs codegenCorrectness accountsRelProps
  venomExecSemantics venomState passSimulationDefs o1PassContract vyperInterpreter frameOutcome callTrace list pair

Triviality linked_halt_effects_transport:
  accounts_agree H tx.target am.accounts
    (process_deletions s.vs_pending_deletions s.vs_accounts) /\
  transient_agree H tx.target am.tStorage s.vs_transient /\
  LIST_REL (request_agree H tx.target) rqs s.vs_requests /\
  dead_result_rel (external_call_dead H tx (res,am,rqs)) (Halt s) (Halt t) ==>
  accounts_agree H tx.target am.accounts
    (process_deletions t.vs_pending_deletions t.vs_accounts) /\
  transient_agree H tx.target am.tStorage t.vs_transient /\
  LIST_REL (request_agree H tx.target) rqs t.vs_requests
Proof
  simp[dead_result_rel_def] >> strip_tac >>
  conj_tac
  >- (`accounts_agree_except (external_call_dead H tx (res,am,rqs))
         (process_deletions t.vs_pending_deletions s.vs_accounts)
         (process_deletions t.vs_pending_deletions t.vs_accounts)` by
        (irule accounts_agree_except_process_deletions >> simp[]) >>
      `!a. (process_deletions t.vs_pending_deletions s.vs_accounts a with
              storage := (process_deletions t.vs_pending_deletions t.vs_accounts a).storage) =
            process_deletions t.vs_pending_deletions t.vs_accounts a /\
            (a <> tx.target ==>
             (process_deletions t.vs_pending_deletions s.vs_accounts a).storage =
             (process_deletions t.vs_pending_deletions t.vs_accounts a).storage)` by
        (gen_tac >>
         qpat_assum `accounts_agree_except _ (process_deletions _ _) _`
           (qspec_then `a` mp_tac o REWRITE_RULE [accounts_agree_except_def]) >>
         Cases_on `a = tx.target` >>
         simp[external_call_dead_def, storage_agree_except_empty]) >>
      `storage_agree (storage_dead H F
           (process_deletions t.vs_pending_deletions s.vs_accounts tx.target).storage)
           (process_deletions t.vs_pending_deletions s.vs_accounts tx.target).storage
           (process_deletions t.vs_pending_deletions t.vs_accounts tx.target).storage` by
        (qpat_assum `accounts_agree_except _ (process_deletions _ _) _`
           (qspec_then `tx.target` mp_tac o REWRITE_RULE [accounts_agree_except_def]) >>
         simp[external_call_dead_def, storage_agree_except_storage_dead]) >>
      irule accounts_agree_storage_dead_trans >>
      qexists_tac `process_deletions t.vs_pending_deletions s.vs_accounts` >>
      gvs[]) >>
  conj_tac
  >- (`!a. a <> tx.target ==> s.vs_transient a = t.vs_transient a` by
        (rpt strip_tac >>
         qpat_assum `transient_agree_except _ _ _`
           (qspec_then `a` mp_tac o REWRITE_RULE [transient_agree_except_def]) >>
         simp[external_call_dead_def, storage_agree_except_empty]) >>
      `storage_agree (storage_dead H T (s.vs_transient tx.target))
          (s.vs_transient tx.target) (t.vs_transient tx.target)` by
        (qpat_assum `transient_agree_except _ _ _`
           (qspec_then `tx.target` mp_tac o REWRITE_RULE [transient_agree_except_def]) >>
         simp[external_call_dead_def, storage_agree_except_storage_dead]) >>
      irule transient_agree_storage_dead_trans >> qexists_tac `s.vs_transient` >> simp[]) >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule (REWRITE_RULE [external_call_dead_def] request_agree_dead_trans) >>
  qexists_tac `EL n s.vs_requests` >>
  fs[external_call_dead_def]
QED

Triviality linked_result_transports:
  external_call_result_rel_mods H mods exps ret tx src vres /\
  dead_result_rel (external_call_dead H tx src) vres vres' ==>
  external_call_result_rel_mods H mods exps ret tx src vres'
Proof
  PairCases_on `src` >> Cases_on `vres` >> Cases_on `vres'` >>
  simp[dead_result_rel_def] >> rpt strip_tac
  >~ [`external_call_result_rel_mods _ _ _ _ _ _ (Abort _ _)`]
  >- (Cases_on `a` >> Cases_on `a'` >> Cases_on `src0` >>
      gvs[external_call_result_rel_mods_def] >>
      Cases_on `y` >> gvs[] >> Cases_on `e` >> gvs[]) >>
  `dead_result_rel (external_call_dead H tx (src0,src1,src2)) (Halt v) (Halt v')` by
    simp[dead_result_rel_def] >>
  `v'.vs_returndata = v.vs_returndata` by
    (irule LIST_EQ >> gvs[external_call_dead_def]) >>
  Cases_on `src0` >> gvs[external_call_result_rel_mods_def, AllCaseEqs()]
  >- (mp_tac (Q.INST [`s` |-> `v`, `t` |-> `v'`, `am` |-> `src1`, `rqs` |-> `src2`]
        (REWRITE_RULE [external_call_dead_def] linked_halt_effects_transport)) >>
      fs[external_call_dead_def]) >>
  Cases_on `y` >> gvs[]
  >- (mp_tac (Q.INST [`s` |-> `v`, `t` |-> `v'`, `am` |-> `src1`, `rqs` |-> `src2`]
        (REWRITE_RULE [external_call_dead_def] linked_halt_effects_transport)) >>
      fs[external_call_dead_def])
QED

Triviality linked_result_terminates:
  external_call_result_rel_mods H mods exps ret tx src res ==> terminates res
Proof
  PairCases_on `src` >> Cases_on `src0` >> Cases_on `res` >>
  simp[external_call_result_rel_mods_def, terminates_def, AllCaseEqs()]
QED

Triviality linked_result_observes_frame:
  external_return_type_mods mods exps tx.function_name = ret /\
  external_call_result_rel_mods
    (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
    mods exps ret tx (call_external (SOME (MAP SND (call_trace es))) gs am tx) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel_at_mods gs mods exps am tx es r es'
Proof
  `log_entry_corresponds
     (build_event_info_mods (type_env_all_modules mods) mods (K NONE))
     (type_env_all_modules mods) tx.target = $=` by
    simp[FUN_EQ_THM, log_entry_corresponds_def] >>
  Cases_on `call_external (SOME (MAP SND (call_trace es))) gs am tx` >>
  rename1 `call_external _ _ am tx = (result,rest)` >> PairCases_on `rest` >>
  Cases_on `result` >> Cases_on `res` >>
  simp[external_call_result_rel_mods_def, call_result_rel_at_mods_def, LET_THM,
       tx_return_bytes_mods_def, effects_agree_def, logs_correspond_def, LIST_REL_eq]
  >- (simp[venom_frame_rel_def] >> rpt strip_tac >>
      qexists_tac `v.vs_returndata` >>
      gvs[logs_correspond_def, LIST_REL_eq]) >>
  Cases_on `y` >> simp[exception_outcome_rel_mods_def] >>
  rpt strip_tac >> gvs[]
  >~ [`unspecified_behaviour_exempt_mods _ _ \/ _`]
  >- (Cases_on `e` >> gvs[]
      >- (drule_then strip_assume_tac venom_frame_rel_abort_failure >> metis_tac[]) >>
      Cases_on `a` >> gvs[] >>
      drule_then strip_assume_tac
        (SRULE [] (Q.INST [`a` |-> `Revert_abort`, `s` |-> `""`]
                     venom_frame_rel_assertion)) >> metis_tac[])
  >~ [`venom_frame_rel _ _ _ (Abort _ _)`]
  >- (irule venom_frame_rel_assertion >> qexistsl_tac [`a`, `v`] >>
      Cases_on `a` >> gvs[]) >>
  gvs[venom_frame_rel_def]
QED

Theorem linked_call_at_horizon_composition:
  run_call es = SOME (r,es') /\ ~frame_resource_starved es r es' /\
  external_return_type_mods mods exps tx.function_name = ret /\
  external_call_result_rel_mods
    (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
    mods exps ret tx (call_external (SOME (MAP SND (call_trace es))) gs am tx)
    (run_context fuel ctx vs) /\
  ctx_sim
    (external_call_dead
      (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
      tx (call_external (SOME (MAP SND (call_trace es))) gs am tx))
    ctx ctx' vs vs' /\
  (!n. ?r' es''. run_call es = SOME (r',es'') /\
    (frame_resource_starved es r' es'' \/
     venom_frame_rel es r' es'' (run_context n ctx' vs'))) ==>
  call_result_rel_at_mods gs mods exps am tx es r es'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac linked_result_terminates >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  qpat_x_assum `!n. ?r' es''. _` (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all_then assume_tac linked_result_transports >>
  irule (Q.INST [`ret` |-> `external_return_type_mods mods exps tx.function_name`,
                 `res` |-> `run_context fuel' ctx' vs'`] linked_result_observes_frame) >>
  simp[] >> qexistsl_tac [`ctx'`, `fuel'`, `vs'`] >> simp[]
QED

Theorem linked_call_at_horizon_static_abort_composition:
  run_call es = SOME (r,es') /\ ~frame_resource_starved es r es' /\
  external_return_type_mods mods exps tx.function_name = ret /\
  external_call_result_rel_mods
    (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
    mods exps ret tx (call_external (SOME (MAP SND (call_trace es))) gs am tx)
    (run_context fuel ctx vs) /\
  ctx_sim
    (external_call_dead
      (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
      tx (call_external (SOME (MAP SND (call_trace es))) gs am tx))
    ctx ctx' vs vs' /\
  (!n. terminates (run_context n ctx vs) ==>
    ?u. run_context n ctx vs = Abort ExHalt_abort u) /\
  (!n a u. run_context n ctx' vs' = Abort a u ==>
    ?r' es''. run_call es = SOME (r',es'') /\
      (frame_resource_starved es r' es'' \/
       ?exc out lgs. frame_outcome es r' es'' (SOME exc) out lgs)) ==>
  call_result_rel_at_mods gs mods exps am tx es r es'
Proof
  rpt strip_tac >>
  drule linked_result_terminates >> strip_tac >>
  qpat_x_assum `!n. terminates _ ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  `?a u'. run_context fuel' ctx' vs' = Abort a u'` by
    (Cases_on `run_context fuel' ctx' vs'` >> gvs[dead_result_rel_def]) >>
  qpat_x_assum `!n a u. _` (qspecl_then [`fuel'`, `a`, `u'`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `external_call_result_rel_mods _ _ _ _ _ src _` >>
  PairCases_on `src` >> gvs[call_result_rel_at_mods_def] >>
  Cases_on `src0` >> gvs[external_call_result_rel_mods_def] >>
  rename1 `call_external _ _ _ _ = (INR source_exc,_,_)` >>
  Cases_on `source_exc` >> gvs[exception_outcome_rel_mods_def] >>
  gvs[AllCaseEqs()]
  >- (Cases_on `e` >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theory concretizeLayoutExternalRequests
Ancestors concretizeLayoutSupplement ptrDiscipline extCallOracle
  venomCallOracleDefs frameRelocationGuardedValues vfmState list pred_set

(* Request snapshots use the final task mask, justified at the emitting step. *)
Theorem concretize_request_observation:
  concretize_supplement D tn s t /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq with <| cr_accounts := rq'.cr_accounts; cr_tStorage := rq'.cr_tStorage |> = rq' ==>
  request_agree_except D rq rq'
Proof
  strip_tac >> simp[request_agree_except_def] >>
  fs[concretize_supplement_def] >> conj_tac
  >- (gvs[accounts_agree_except_def] >> gen_tac >>
      first_x_assum (qspec_then `a` strip_assume_tac) >> simp[] >>
      gvs[storage_agree_except_def, word_agree_except_def, key_taint_def, SUBSET_DEF] >>
      Cases_on `a = s.vs_call_ctx.cc_address` >> gvs[] >> metis_tac[]) >>
  gvs[transient_agree_except_def, storage_agree_except_def,
      word_agree_except_def, key_taint_def, SUBSET_DEF] >> gen_tac >>
  Cases_on `a = s.vs_call_ctx.cc_address` >> gvs[] >> metis_tac[]
QED

(* Accounts/transient snapshots do not determine which oracle item is consumed. *)
Theorem request_agree_take_outcome:
  rq with <| cr_accounts := rq'.cr_accounts; cr_tStorage := rq'.cr_tStorage |> = rq' ==>
  SND (take_outcome rq os) = SND (take_outcome rq' os) /\
  (FST (take_outcome rq os)).co_success = (FST (take_outcome rq' os)).co_success /\
  (FST (take_outcome rq os)).co_returnData = (FST (take_outcome rq' os)).co_returnData /\
  (FST (take_outcome rq os)).co_created = (FST (take_outcome rq' os)).co_created /\
  (FST (take_outcome rq os)).co_logs = (FST (take_outcome rq' os)).co_logs /\
  (FST (take_outcome rq os)).co_toDelete = (FST (take_outcome rq' os)).co_toDelete
Proof
  strip_tac >>
  `rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
   rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data` by
    fs[request_agree_except_def, call_request_component_equality] >>
  `computed_precompile rq = computed_precompile rq'` by
    simp[computed_precompile_def] >>
  Cases_on `os` >> simp[take_outcome_def] >>
  Cases_on `computed_precompile rq'` >> simp[] >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >> simp[] >>
  Cases_on `x` >> simp[] >> Cases_on `h.co_success` >> simp[]
QED

Theorem request_agree_record_request:
  request_agree_except D rq rq' /\
  LIST_REL (request_agree_except D) rqs rqs' ==>
  LIST_REL (request_agree_except D)
    (record_request rq rqs) (record_request rq' rqs')
Proof
  strip_tac >>
  `computed_precompile rq = computed_precompile rq'` by
    fs[computed_precompile_def, request_agree_except_def,
       call_request_component_equality] >>
  simp[record_request_def] >> Cases_on `computed_precompile rq'` >> simp[]
QED

Theorem request_agree_adopt_outcome:
  request_agree_except D rq rq' /\
  adopt_outcome rq (FST (take_outcome rq os))
    (rq.cr_accounts, rq.cr_tStorage, logs) = (ac,ts,lg) /\
  adopt_outcome rq' (FST (take_outcome rq' os))
    (rq'.cr_accounts, rq'.cr_tStorage, logs) = (ac',ts',lg') ==>
  accounts_agree_except D ac ac' /\ transient_agree_except D ts ts' /\ lg = lg'
Proof
  strip_tac >>
  `rq.cr_kind = rq'.cr_kind /\ rq.cr_static = rq'.cr_static /\
   computed_precompile rq = computed_precompile rq'` by
    fs[computed_precompile_def, request_agree_except_def,
       call_request_component_equality] >>
  Cases_on `computed_precompile rq`
  >- (drule adopt_outcome_computed >>
      disch_then (qspecl_then [`os`,`logs`] assume_tac) >>
      `computed_precompile rq'` by metis_tac[] >>
      drule adopt_outcome_computed >>
      disch_then (qspecl_then [`os`,`logs`] assume_tac) >>
      gvs[request_agree_except_def]) >>
  Cases_on `os`
  >- gvs[take_outcome_def, adopt_outcome_def, request_agree_except_def] >>
  gvs[take_outcome_def, adopt_outcome_def] >>
  Cases_on `~rq'.cr_static /\ (h.co_success \/ rq'.cr_kind <> MessageCall)` >>
  gvs[request_agree_except_def, accounts_agree_except_def,
      transient_agree_except_def, storage_agree_except_def, word_agree_except_def]
QED

Theorem concretize_supplement_clean_accounts:
  concretize_supplement D tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >>
  `!st st'. storage_agree_except {} st st' ==> st = st'` by
    (simp[storage_agree_except_def, key_taint_def] >> rpt strip_tac >>
     simp[FUN_EQ_THM] >> gen_tac >> irule word_agree_except_empty >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
  fs[concretize_supplement_def, accounts_agree_except_def,
     transient_agree_except_def] >>
  conj_tac >> simp[FUN_EQ_THM] >> gen_tac
  >- (qpat_x_assum `!a. _ /\ _` (qspec_then `x` strip_assume_tac) >>
      `(s.vs_accounts x).storage = (t.vs_accounts x).storage` by metis_tac[] >>
      gvs[account_state_component_equality]) >>
  metis_tac[]
QED

val _ = export_theory();

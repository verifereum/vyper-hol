Theory concretizeLayoutExternalCall
Ancestors concretizeLayoutExternalRequests concretizeLayoutSupplement
  venomCallOracleDefs extCallOracle ptrDiscipline venomState venomExecSemantics
  venomInst list pred_set

(* Expose state fields without expanding oracle selection or adoption. *)
Theorem call_completion_fields:
  consume_call_outcome rq ro rs s = (w,post) /\
  take_outcome rq s.vs_outcomes = (oc,rest) /\
  adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs) = (ac,ts,lg) ==>
  w = (if oc.co_success then 1w else 0w) /\
  post.vs_requests = record_request rq s.vs_requests /\
  post.vs_outcomes = rest /\ post.vs_accounts = ac /\
  post.vs_transient = ts /\ post.vs_logs = lg /\
  post.vs_pending_deletions = adopt_outcome_deletions rq oc s.vs_pending_deletions /\
  post.vs_returndata = oc.co_returnData /\
  post.vs_memory = (write_memory_with_expansion ro (TAKE rs oc.co_returnData) s).vs_memory /\
  post.vs_call_ctx = s.vs_call_ctx /\
  post.vs_immutables = s.vs_immutables /\
  post.vs_halted = s.vs_halted
Proof
  strip_tac >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = _` mp_tac >>
  simp[consume_call_outcome_def, Excl "consume_call_outcome_eq"] >>
  strip_tac >> gvs[]
QED

(* The reset test uses observable list changes, not state-record equality. *)
Theorem call_adoption_reset:
  rq.cr_kind = MessageCall /\
  take_outcome rq os = (oc,rest) /\
  adopt_outcome rq oc (rq.cr_accounts,rq.cr_tStorage,logs) = (ac,ts,lg) ==>
  ((~rq.cr_static /\ record_request rq rqs <> rqs /\ rest <> os /\
     (HD os).co_success) <=>
   (~rq.cr_static /\ ~computed_precompile rq /\ os <> [] /\ (HD os).co_success)) /\
  (ac,ts) =
    if ~rq.cr_static /\ ~computed_precompile rq /\ os <> [] /\ (HD os).co_success
    then (oc.co_accounts,oc.co_tStorage)
    else (rq.cr_accounts,rq.cr_tStorage)
Proof
  strip_tac >> Cases_on `computed_precompile rq`
  >- (drule adopt_outcome_computed >>
      disch_then (qspecl_then [`os`,`logs`] mp_tac) >>
      simp[] >> strip_tac >> gvs[record_request_def]) >>
  Cases_on `os`
  >- gvs[take_outcome_def, failed_outcome_def, adopt_outcome_def] >>
  gvs[take_outcome_def, record_request_def, adopt_outcome_def] >>
  Cases_on `rq.cr_static` >> Cases_on `h.co_success` >> gvs[]
QED

(* Successful noncomputed calls replace both snapshots identically, so
   their storage masks may be cleared rather than merely preserved. *)
Theorem call_adoption_reset_agreement:
  request_agree_except M rq rq' /\ rq.cr_kind = MessageCall /\
  take_outcome rq os = (oc,rest) /\ take_outcome rq' os = (oc',rest') /\
  adopt_outcome rq oc (rq.cr_accounts,rq.cr_tStorage,logs) = (ac,ts,lg) /\
  adopt_outcome rq' oc' (rq'.cr_accounts,rq'.cr_tStorage,logs) = (ac',ts',lg') ==>
  accounts_agree_except
    (M with d_stor := if ~rq.cr_static /\ ~computed_precompile rq /\
                         os <> [] /\ (HD os).co_success
                      then K (K {}) else M.d_stor) ac ac' /\
  transient_agree_except
    (M with d_trans := if ~rq.cr_static /\ ~computed_precompile rq /\
                          os <> [] /\ (HD os).co_success
                       then K (K {}) else M.d_trans) ts ts'
Proof
  strip_tac >>
  `rq.cr_kind = rq'.cr_kind /\ rq.cr_static = rq'.cr_static /\
   computed_precompile rq = computed_precompile rq'` by
    fs[request_agree_except_def, computed_precompile_def,
       call_request_component_equality] >>
  Cases_on `computed_precompile rq`
  >- (drule adopt_outcome_computed >>
      disch_then (qspecl_then [`os`,`logs`] assume_tac) >>
      `computed_precompile rq'` by metis_tac[] >>
      drule adopt_outcome_computed >>
      disch_then (qspecl_then [`os`,`logs`] assume_tac) >>
      gvs[request_agree_except_def, accounts_agree_except_def,
          transient_agree_except_def]) >>
  Cases_on `os`
  >- gvs[take_outcome_def, failed_outcome_def, adopt_outcome_def,
         request_agree_except_def, accounts_agree_except_def,
         transient_agree_except_def] >>
  gvs[take_outcome_def, adopt_outcome_def] >>
  Cases_on `rq.cr_static` >> Cases_on `h.co_success` >>
  gvs[request_agree_except_def, accounts_agree_except_def,
      transient_agree_except_def, storage_agree_except_def, word_agree_except_def]
QED

Theorem call_completion_taint_masks:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  rq.cr_kind = MessageCall /\
  rq.cr_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  consume_call_outcome rq ro rs s = (w,post) /\
  take_outcome rq s.vs_outcomes = (oc,rest) /\
  adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs) = (ac,ts,lg) ==>
  (step_taint inst s post tn).t_stor =
    (if ~rq.cr_static /\ ~computed_precompile rq /\ s.vs_outcomes <> [] /\
        (HD s.vs_outcomes).co_success then {} else tn.t_stor) /\
  (step_taint inst s post tn).t_trans =
    (if ~rq.cr_static /\ ~computed_precompile rq /\ s.vs_outcomes <> [] /\
        (HD s.vs_outcomes).co_success then {} else tn.t_trans) /\
  (step_taint inst s post tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all call_completion_fields >> strip_tac >>
  `adopt_outcome rq oc (rq.cr_accounts,rq.cr_tStorage,s.vs_logs) = (ac,ts,lg)` by
    metis_tac[] >>
  drule_all call_adoption_reset >>
  disch_then (qspec_then `s.vs_requests` strip_assume_tac) >>
  gvs[step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def, MEM,
      Excl "consume_call_outcome_eq"]
QED

val _ = export_theory();

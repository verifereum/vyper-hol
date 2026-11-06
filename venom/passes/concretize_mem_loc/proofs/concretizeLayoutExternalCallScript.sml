Theory concretizeLayoutExternalCall
Ancestors concretizeLayoutExternalRequests concretizeLayoutSupplement
  venomCallOracleDefs extCallOracle ptrDiscipline venomState venomExecSemantics
  venomInst list pred_set frameRelocationStoreSteps frameRelocationGhostCopy
  frameRelocationAllocationSteps frameRelocationLocal frameRelocationValues
  frameRelocationOpaque frameRelocationMemory frameRelocationGuardedValues
  frameOriginUpdates finite_map frameRelocationCleanOperands o1PassContract
  pointerConfinedDefs memLocDefs concretizeLayoutLocalCalldataCopy
  frameRelocationTaintOrder frameRelocationCopyTaint
  frameRelocationReachableSupport frameResolvedTrace frameOriginReachable
  frameOriginHistory frameJointTransition frameJointDemand frameJointTrace
  frameActivationLookup frameActivationLifetime concretizeLayoutReaderContext
  frameRelocationEnvironment contextCodegenRel words concretizeLayoutLocalSha3
  concretizeLayoutLocalReturnCopy

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
  post.vs_halted = s.vs_halted /\
  post.vs_vars = s.vs_vars /\ post.vs_allocas = s.vs_allocas /\
  post.vs_fmp = s.vs_fmp /\ post.vs_labels = s.vs_labels /\
  post.vs_gas_readings = s.vs_gas_readings /\
  post.vs_tx_ctx = s.vs_tx_ctx /\ post.vs_block_ctx = s.vs_block_ctx /\
    post.vs_prev_hashes = s.vs_prev_hashes /\
  post.vs_code = s.vs_code /\ post.vs_data_section = s.vs_data_section
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

Theorem concretize_call_completion_supplement:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  concretize_supplement D tn s t /\
  rq.cr_kind = MessageCall /\
  rq.cr_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq with <| cr_accounts := rq'.cr_accounts; cr_tStorage := rq'.cr_tStorage |> = rq' /\
  (~computed_precompile rq ==> request_agree_except D rq rq') /\ s.vs_logs = t.vs_logs /\
  consume_call_outcome rq ro rs s = (w,post) /\
  consume_call_outcome rq' ro' rs t = (w',post') ==>
  w = w' /\ concretize_supplement D (step_taint inst s post tn) post post'
Proof
  strip_tac >>
  qabbrev_tac `M = D with <|
    d_stor := (\a st. if a = s.vs_call_ctx.cc_address then tn.t_stor else {});
    d_trans := (\a st. if a = s.vs_call_ctx.cc_address then tn.t_trans else {}) |>` >>
  `request_agree_except M rq rq'` by
    fs[request_agree_except_def, concretize_supplement_def, Abbr `M`,
       accounts_agree_except_def, transient_agree_except_def] >>
  `computed_precompile rq = computed_precompile rq'` by
    fs[request_agree_except_def, computed_precompile_def,
       call_request_component_equality] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
  Cases_on `take_outcome rq s.vs_outcomes` >>
  Cases_on `take_outcome rq' s.vs_outcomes` >>
  rename1 `take_outcome rq s.vs_outcomes = (oc,rest)` >>
  rename1 `take_outcome rq' s.vs_outcomes = (ocT,restT)` >>
  Cases_on `adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >>
  rename1 `adopt_outcome rq oc _ = (ac,ats,alg)` >>
  Cases_on `adopt_outcome rq' ocT (t.vs_accounts,t.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >>
  rename1 `adopt_outcome rq' ocT _ = (acT,atsT,algT)` >>
  drule_all call_completion_fields >> strip_tac >>
  `take_outcome rq' t.vs_outcomes = (ocT,restT)` by metis_tac[] >>
  `adopt_outcome rq' ocT (t.vs_accounts,t.vs_transient,t.vs_logs) = (acT,atsT,algT)` by
    metis_tac[] >>
  drule_all call_completion_fields >> strip_tac >>
  drule request_agree_take_outcome >>
  disch_then (qspec_then `s.vs_outcomes` mp_tac) >> simp[] >> strip_tac >>
  drule_all call_completion_taint_masks >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  `adopt_outcome rq oc (rq.cr_accounts,rq.cr_tStorage,s.vs_logs) = (ac,ats,alg)` by
    metis_tac[] >>
  `adopt_outcome rq' ocT (rq'.cr_accounts,rq'.cr_tStorage,s.vs_logs) = (acT,atsT,algT)` by
    metis_tac[] >>
  drule_all call_adoption_reset_agreement >> strip_tac >>
  `LIST_REL (request_agree_except D)
    (record_request rq s.vs_requests) (record_request rq' t.vs_requests)` by
    (Cases_on `computed_precompile rq`
     >- (`computed_precompile rq'` by
           metis_tac[] >>
         fs[record_request_def, concretize_supplement_def]) >>
     irule request_agree_record_request >> fs[concretize_supplement_def]) >>
  qpat_x_assum `consume_call_outcome rq _ _ _ = _` kall_tac >>
  qpat_x_assum `consume_call_outcome rq' _ _ _ = _` kall_tac >>
  qpat_x_assum `MEM _ _` kall_tac >>
  Cases_on `~rq.cr_static /\ ~computed_precompile rq /\ s.vs_outcomes <> [] /\
            (HD s.vs_outcomes).co_success` >>
  gvs[concretize_supplement_def, Abbr `M`, accounts_agree_except_def,
      transient_agree_except_def, Excl "consume_call_outcome_eq"]
QED

Theorem concretize_call_completion_observation:
  concretize_local_obs s t /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  rq with <| cr_accounts := rq'.cr_accounts; cr_tStorage := rq'.cr_tStorage |> = rq' /\
  s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome rq ro rs s = (w,post) /\
  consume_call_outcome rq' ro' rs t = (w',post') ==>
  w = w' /\ concretize_local_obs post post' /\
  post.vs_vars = s.vs_vars /\ post'.vs_vars = t.vs_vars
Proof
  strip_tac >>
  qabbrev_tac `M = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                     d_imm := K UNIV; d_ret := K {} |>` >>
  `request_agree_except M rq rq' /\
   LIST_REL (request_agree_except M) s.vs_requests t.vs_requests /\
   s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions /\
   s.vs_halted = t.vs_halted /\
   imms_agree_except M s.vs_immutables t.vs_immutables` by
    fs[concretize_local_obs_def, dead_result_rel_def, request_agree_except_def,
       Abbr `M`] >>
  Cases_on `take_outcome rq s.vs_outcomes` >>
  Cases_on `take_outcome rq' s.vs_outcomes` >>
  rename1 `take_outcome rq s.vs_outcomes = (oc,rest)` >>
  rename1 `take_outcome rq' s.vs_outcomes = (ocT,restT)` >>
  Cases_on `adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >> rename1 `adopt_outcome rq oc _ = (ac,ats,alg)` >>
  Cases_on `adopt_outcome rq' ocT (t.vs_accounts,t.vs_transient,t.vs_logs)` >>
  PairCases_on `r` >> rename1 `adopt_outcome rq' ocT _ = (acT,atsT,algT)` >>
  drule_all call_completion_fields >> strip_tac >>
  `take_outcome rq' t.vs_outcomes = (ocT,restT)` by metis_tac[] >>
  drule_all call_completion_fields >> strip_tac >>
  drule request_agree_take_outcome >>
  disch_then (qspec_then `s.vs_outcomes` mp_tac) >> simp[] >> strip_tac >>
  `adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
     (rq.cr_accounts,rq.cr_tStorage,s.vs_logs) = (ac,ats,alg)` by
    (fs[] >> metis_tac[]) >>
  `adopt_outcome rq' (FST (take_outcome rq' s.vs_outcomes))
     (rq'.cr_accounts,rq'.cr_tStorage,s.vs_logs) = (acT,atsT,algT)` by
    (fs[] >> metis_tac[]) >>
  drule_all request_agree_adopt_outcome >> strip_tac >>
  drule_all request_agree_record_request >> strip_tac >>
  qpat_x_assum `consume_call_outcome rq _ _ _ = _` kall_tac >>
  qpat_x_assum `consume_call_outcome rq' _ _ _ = _` kall_tac >>
  `rq.cr_static = rq'.cr_static /\ rq.cr_kind = rq'.cr_kind` by
    fs[request_agree_except_def, call_request_component_equality] >>
  qpat_x_assum `rq with <| cr_accounts := _; cr_tStorage := _ |> = _` kall_tac >>
  fs[Abbr `M`, Excl "consume_call_outcome_eq"] >>
  simp[concretize_local_obs_def, dead_result_rel_def,
       adopt_outcome_deletions_def, Excl "consume_call_outcome_eq"]
QED

Theorem ext_call_success_envelope[local]:
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post ==>
  ?out w p. inst.inst_outputs = [out] /\
    consume_call_outcome (venom_call_request s addr value off sz is_static)
      (w2n ro) (w2n rs) s = (w,p) /\ post = update_var out w p
Proof
  simp[exec_ext_call_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  strip_tac >> pairarg_tac >> gvs[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  metis_tac[]
QED

Theorem concretize_ext_call_observation:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  is_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (~computed_precompile (venom_call_request s addr value off sz is_static) ==>
    tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)) /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n (offT:bytes32)) (w2n sz) t /\
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post ==>
  ?post'. exec_ext_call inst t gas addr value (offT:bytes32) sz (roT:bytes32) rs is_static = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)
Proof
  strip_tac >>
  qabbrev_tac `rq = venom_call_request s addr value off sz is_static` >>
  qabbrev_tac `rqT = venom_call_request t addr value offT sz is_static` >>
  `rq.cr_accounts = s.vs_accounts /\ rqT.cr_accounts = t.vs_accounts /\
   rq.cr_tStorage = s.vs_transient /\ rqT.cr_tStorage = t.vs_transient /\
   rq.cr_kind = MessageCall /\
   rq.cr_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
   rq with <|cr_accounts := rqT.cr_accounts; cr_tStorage := rqT.cr_tStorage|> = rqT` by
    (simp[Abbr `rq`, Abbr `rqT`, venom_call_request_def] >> metis_tac[]) >>
  `~computed_precompile rq ==> request_agree_except D rq rqT` by
    (strip_tac >>
     `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
       (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
      tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
       (s.vs_transient s.vs_call_ctx.cc_address)` by metis_tac[] >>
     drule_all concretize_request_observation >> simp[]) >>
  drule ext_call_success_envelope >> strip_tac >>
  `consume_call_outcome rq (w2n ro) (w2n rs) s = (w,p)` by
    fs[Abbr `rq`, Excl "consume_call_outcome_eq"] >>
  Cases_on `consume_call_outcome rqT (w2n roT) (w2n rs) t` >>
  rename1 `consume_call_outcome rqT _ _ t = (wT,pT)` >>
  `s.vs_logs = t.vs_logs` by fs[concretize_local_obs_def, dead_result_rel_def] >>
  drule_all concretize_call_completion_supplement >> strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
  drule_all concretize_call_completion_observation >> strip_tac >>
  qexists_tac `update_var out wT pT` >> conj_tac
  >- (gvs[Abbr `rqT`, Excl "consume_call_outcome_eq"] >>
      simp[exec_ext_call_def, Excl "consume_call_outcome_eq"]) >>
  conj_tac
  >- gvs[concretize_local_obs_def, dead_result_rel_def, update_var_def,
         Excl "consume_call_outcome_eq"] >>
  conj_tac
  >- (qpat_x_assum `concretize_supplement D (step_taint _ _ _ _) _ _` mp_tac >>
  simp[concretize_supplement_def, step_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, update_var_def,
       Excl "consume_call_outcome_eq"] >>
  strip_tac >> fs[Excl "consume_call_outcome_eq"]) >>
  qexistsl_tac [`out`,`w`] >> simp[update_var_def]
QED

Theorem ext_call_execution_fields:
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post ==>
  ?out w. inst.inst_outputs = [out] /\ (w = 0w \/ w = 1w) /\
    post.vs_vars = (update_var out w s).vs_vars /\
    post.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rs) post.vs_returndata) s).vs_memory /\
    post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp /\
    post.vs_labels = s.vs_labels /\ post.vs_call_ctx = s.vs_call_ctx /\
    post.vs_gas_readings = s.vs_gas_readings /\
    post.vs_tx_ctx = s.vs_tx_ctx /\ post.vs_block_ctx = s.vs_block_ctx /\
    post.vs_prev_hashes = s.vs_prev_hashes /\
    post.vs_code = s.vs_code /\ post.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule ext_call_success_envelope >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_call_outcome rq _ _ s = _` >>
  Cases_on `take_outcome rq s.vs_outcomes` >>
  rename1 `take_outcome rq s.vs_outcomes = (oc,rest)` >>
  Cases_on `adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >> drule_all call_completion_fields >> strip_tac >>
  qexistsl_tac [`out`,`w`] >>
  gvs[update_var_def, Excl "consume_call_outcome_eq"] >>
  Cases_on `oc.co_success` >> simp[]
QED


Theorem ext_call_memory[local]:
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post ==>
  post.vs_memory = (write_memory_with_expansion (w2n ro)
    (TAKE (w2n rs) post.vs_returndata) s).vs_memory
Proof
  metis_tac[ext_call_execution_fields]
QED



Theorem concretize_ext_call_local_execution:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  is_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (~computed_precompile (venom_call_request s addr value off sz is_static) ==>
    tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)) /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n (offT:bytes32)) (w2n sz) t /\
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post /\
  (!a b. next a b /\ w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
     b = w2n (roT:bytes32) + (a-w2n ro)) /\
  (!a b. next a b /\ ~(w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
     R a b /\ ~(w2n roT <= b /\
       b < w2n roT + LENGTH (TAKE (w2n rs) post.vs_returndata))) ==>
  ?post'. exec_ext_call inst t gas addr value offT sz roT rs is_static = OK post' /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes Opaque (origin_set rv inst.inst_outputs NONE) (step_taint inst s post tn))
      next concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post'
Proof
  strip_tac >>
  `concretize_local_obs s t` by metis_tac[local_rel_observation] >>
  `?post'. exec_ext_call inst t gas addr value offT sz roT rs is_static = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)` by
    (irule concretize_ext_call_observation >>
     simp[] >> qexistsl_tac [`off`,`ro`] >> gvs[]) >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  `post.vs_returndata = post'.vs_returndata` by
    (fs[concretize_local_obs_def, dead_result_rel_def] >>
     irule listTheory.LIST_EQ >> simp[]) >>
  `demand_agree next (\a. read_byte a post.vs_memory)
    (\b. read_byte b post'.vs_memory)` by suspend "memory" >>
  `local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R (\s t. T) s t` by fs[local_rel_def] >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [out] NONE))
    (guarded_bytes Opaque (origin_set rv [out] NONE) (step_taint inst s post tn))
    R (\s t. T) (update_var out w s) (update_var out w t)` by suspend "values" >>
  fs[local_rel_def, variable_domains_def, variables_agree_on_def,
     local_values_def, lookup_var_def, update_var_def]
QED
Resume concretize_ext_call_local_execution[memory]:
  qpat_assum `exec_ext_call _ s _ _ _ _ _ _ _ _ = OK post`
    (mp_tac o MATCH_MP ext_call_memory) >>
  qpat_assum `exec_ext_call _ t _ _ _ _ _ _ _ _ = OK post'`
    (mp_tac o MATCH_MP ext_call_memory) >>
  rpt strip_tac >>
  qpat_x_assum `post.vs_returndata = post'.vs_returndata` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> irule demand_agree_write_memory >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!a b. _ ==> b = _`
      (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  qexists_tac `R` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a b. _ ==> R a b /\ _`
        (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[local_rel_demand]
QED
Resume concretize_ext_call_local_execution[values]:
  irule local_rel_update >> simp[] >>
  (conj_tac >- simp[guarded_bytes_def, frameRelocationGhostCopyTheory.copy_bytes_def,
    word_agree_except_def]) >>
  (conj_tac >- simp[guarded_ptr_def, copy_ptr_def, origin_set_lookup]) >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def,
    frameRelocationGhostCopyTheory.copy_bytes_def, origin_set_lookup,
    step_taint_def, set_var_taint_def, out_taint_def, MEM, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[op_taint_def, FLOOKUP_UPDATE]
QED
Finalise concretize_ext_call_local_execution
Theorem ext_call_base_envelope[local]:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  step_inst_base inst s = OK post ==>
  ?opg opa vals opd opn opr opm gas addr value off sz ro rs.
    inst.inst_operands = [opg;opa] ++ vals ++ [opd;opn;opr;opm] /\
    ((inst.inst_opcode = CALL /\ ?opv. vals = [opv] /\
       eval_operand opv s = SOME value /\
       ~(s.vs_call_ctx.cc_static /\ value <> 0w)) \/
     (inst.inst_opcode = STATICCALL /\ vals = [] /\ value = 0w)) /\
    eval_operand opg s = SOME gas /\ eval_operand opa s = SOME addr /\
    eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
    eval_operand opr s = SOME ro /\ eval_operand opm s = SOME rs /\
    exec_ext_call inst s gas addr value off sz ro rs
      (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) = OK post
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  fs[MEM] >> asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  rpt strip_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  metis_tac[]
QED

Theorem ext_call_scalar_agreement[local]:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  inst.inst_operands = [opg;opa] ++ vals ++ [opd;opn;opr;opm] /\
  ((inst.inst_opcode = CALL /\ LENGTH vals = 1) \/
   (inst.inst_opcode = STATICCALL /\ vals = [])) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  !op. MEM op ([opg;opa;opn;opm] ++ vals) ==>
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> Cases_on `vals` >> gvs[] >> rpt strip_tac >>
  `!v. op = Var v ==> FLOOKUP rv v = NONE` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `v IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     qpat_x_assum `!v. _ ==> _` (qspec_then `v` mp_tac) >>
     Cases_on `opd = Var v` >> Cases_on `opr = Var v` >>
     Cases_on `opg = Var v` >> Cases_on `opa = Var v` >>
     Cases_on `opn = Var v` >> Cases_on `opm = Var v` >>
     gvs[] >> Cases_on `h = Var v` >> gvs[] >> rpt strip_tac >> gvs[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
  disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >> (conj_tac >- metis_tac[]) >>
  qexists_tac `inst` >> simp[] >> fs[] >> metis_tac[]
QED

Theorem ext_call_prov[local]:
  MEM inst.inst_opcode [CALL; STATICCALL] /\ inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst post =
    SND o_f (origin_set rv inst.inst_outputs NONE)
Proof
  strip_tac >> fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
       fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  rpt gen_tac >> Cases_on `x = v` >> simp[]
QED

(* Pure transport for clean output prefixes and synchronized snapshot reset. *)
Theorem concretize_reset_write_taint_order[local]:
  relocation_taint_le R tn un /\
  (!a b. next a b /\ a IN written ==> b IN writtenT) /\
  (!a b. next a b /\ a NOTIN written ==> R a b) ==>
  relocation_taint_le next
    (tn with <|t_mem := tn.t_mem DIFF written;
       t_var := tn.t_var |+ (v,{});
       t_stor := if reset then {} else tn.t_stor;
       t_trans := if reset then {} else tn.t_trans|>)
    (un with <|t_mem := un.t_mem DIFF writtenT;
       t_var := un.t_var |+ (v,{});
       t_stor := if reset then {} else un.t_stor;
       t_trans := if reset then {} else un.t_trans|>)
Proof
  strip_tac >> fs[relocation_taint_le_def] >>
  simp[relocation_taint_le_def] >> conj_tac
  >- (fs[demand_taint_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[op_taint_def, FLOOKUP_UPDATE] >> rpt gen_tac >>
      IF_CASES_TAC >> simp[] >> fs[op_taint_def]) >>
  Cases_on `reset` >> simp[]
QED

Theorem ext_call_taint[local]:
  MEM inst.inst_opcode [CALL; STATICCALL] /\ inst.inst_outputs = [v] /\
  inst.inst_operands = [opg;opa] ++ vals ++ [opd;opn;opr;opm] /\
  (vals = [] \/ ?opv. vals = [opv]) /\
  post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp ==>
  step_taint inst s post tn =
    tn with <|t_mem := tn.t_mem DIFF range_bytes (step_writes inst s post);
      t_var := tn.t_var |+ (v,{});
      t_stor := adopt_reset inst
        (~s.vs_call_ctx.cc_static /\ post.vs_requests <> s.vs_requests /\
         post.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_stor;
      t_trans := adopt_reset inst
        (~s.vs_call_ctx.cc_static /\ post.vs_requests <> s.vs_requests /\
         post.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_trans|>
Proof
  strip_tac >>
  `new_site_bytes s post = {}` by
    (irule new_site_bytes_unchanged >> simp[]) >>
  fs[MEM] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, out_taint_def,
       set_var_taint_def, store_taint_def, imm_taint_def,
       taint_component_equality]
QED


(* Observable requests grow exactly on noncomputed calls. *)
Theorem ext_call_execution_request_growth:
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post ==>
  (LENGTH s.vs_requests < LENGTH post.vs_requests <=>
   ~computed_precompile (venom_call_request s addr value off sz is_static))
Proof
  strip_tac >> drule ext_call_success_envelope >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_call_outcome rq _ _ s = _` >>
  Cases_on `take_outcome rq s.vs_outcomes` >>
  rename1 `take_outcome rq s.vs_outcomes = (oc,rest)` >>
  Cases_on `adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >> drule_all call_completion_fields >> strip_tac >>
  simp[update_var_def, record_request_def] >> IF_CASES_TAC >> simp[]
QED

Theorem ext_call_execution_taint_masks:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  is_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post ==>
  (step_taint inst s post tn).t_stor =
    (if ~is_static /\
        ~computed_precompile (venom_call_request s addr value off sz is_static) /\
        s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success
     then {} else tn.t_stor) /\
  (step_taint inst s post tn).t_trans =
    (if ~is_static /\
        ~computed_precompile (venom_call_request s addr value off sz is_static) /\
        s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success
     then {} else tn.t_trans)
Proof
  strip_tac >> drule ext_call_success_envelope >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_call_outcome rq _ _ s = _` >>
  `rq.cr_kind = MessageCall /\
   rq.cr_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
   rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient` by
    (simp[Abbr `rq`, venom_call_request_def] >> metis_tac[]) >>
  Cases_on `take_outcome rq s.vs_outcomes` >>
  rename1 `take_outcome rq s.vs_outcomes = (oc,rest)` >>
  Cases_on `adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >> drule_all call_completion_taint_masks >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  gvs[step_taint_def, store_taint_def, adopt_reset_def, update_var_def,
      Abbr `rq`, venom_call_request_def, Excl "consume_call_outcome_eq"]
QED

Theorem ext_call_execution_reset_agreement:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  is_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  s.vs_outcomes = t.vs_outcomes /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  exec_ext_call inst s (gas:bytes32) (addr:bytes32) (value:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) is_static = OK post /\
  exec_ext_call inst t gas addr value (offT:bytes32) sz (roT:bytes32) rs is_static = OK post' ==>
  ?reset.
    (step_taint inst s post tn).t_stor = (if reset then {} else tn.t_stor) /\
    (step_taint inst t post' un).t_stor = (if reset then {} else un.t_stor) /\
    (step_taint inst s post tn).t_trans = (if reset then {} else tn.t_trans) /\
    (step_taint inst t post' un).t_trans = (if reset then {} else un.t_trans)
Proof
  strip_tac >>
  `computed_precompile (venom_call_request s addr value off sz is_static) =
   computed_precompile (venom_call_request t addr value offT sz is_static)` by
    simp[computed_precompile_def, venom_call_request_def] >>
  `is_static = (inst.inst_opcode = STATICCALL \/ t.vs_call_ctx.cc_static)` by
    metis_tac[] >>
  drule_all ext_call_execution_taint_masks >>
  disch_then (qspec_then `un` strip_assume_tac) >>
  rev_drule_all ext_call_execution_taint_masks >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  qexists_tac `~is_static /\
    ~computed_precompile (venom_call_request s addr value off sz is_static) /\
    s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success` >> simp[]
QED

Theorem concretize_ext_call_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\ taint_within D C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  MEM inst.inst_opcode [CALL; STATICCALL] ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    step_prov PG G inst post = SND o_f (origin_set rv inst.inst_outputs NONE) /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gnvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `step_inst_base inst s = OK post` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def] >> fs[MEM]) >>
  drule_all (SRULE [MEM] ext_call_base_envelope) >> strip_tac >> (
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!op. MEM op ([opg;opa;opn;opm] ++ vals) ==>
    eval_operand op s = eval_operand op t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) ext_call_scalar_agreement >>
     disch_then assume_tac >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     (conj_tac >- (qexists_tac `P` >> simp[])) >>
     (conj_tac >- (qexists_tac `C` >> simp[])) >>
     goal_assum (drule_at (Pat `_ .inst_operands = _`)) >> fs[]) >>
  `MEM (w2n off,w2n sz) (source_memory_read_ranges inst s)` by
    (gvs[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  `?offT. eval_operand opd t = SOME offT /\
     (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
       joint_relocation_demand lo (concretize_positions C') q0 es qs c
         (w2n off+i) (w2n offT+i))` by
    (irule concretize_read_demand_geometry >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def] >> metis_tac[]) >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t` by
    ((simp[read_memory_def] >> irule listTheory.LIST_EQ >>
      simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
      qx_gen_tac `j` >> strip_tac >>
      `w2n off+j NOTIN tn.t_mem` by
        (fs[taint_ok_def, about_to_revert_def] >>
         first_x_assum (qspecl_then [`w2n off`,`w2n sz`,`w2n off+j`] mp_tac) >>
         simp[] >> fs[]) >>
      `codegenRel$read_byte (w2n off+j) s.vs_memory =
       codegenRel$read_byte (w2n offT+j) t.vs_memory` by
        (drule local_rel_demand >> simp[frameRelocationDemandTheory.demand_agree_def] >>
         metis_tac[arithmeticTheory.ADD_COMM]) >>
      fs[codegenRelTheory.read_byte_def] >> simp[EL_TAKE] >>
      Cases_on `w2n off+j < LENGTH s.vs_memory` >>
      Cases_on `w2n offT+j < LENGTH t.vs_memory` >>
      gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
          LENGTH_DROP, rich_listTheory.EL_DROP, rich_listTheory.EL_REPLICATE])) >>
  `~computed_precompile (venom_call_request s addr value off sz
      (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static)) ==>
    tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (strip_tac >>
     `LENGTH s.vs_requests < LENGTH post.vs_requests` by
       (drule ext_call_execution_request_growth >> simp[]) >>
     `active_inst fn inst s` by
       (fs[joint_config_reachable_def] >>
        metis_tac[joint_origin_history_projection, frameHistoryDefinitionsTheory.frame_history_active]) >>
     fs[taint_within_def] >> first_x_assum irule >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     simp[step_inst_def] >> fs[]) >>
  `post.vs_allocas = s.vs_allocas` by metis_tac[ext_call_execution_fields] >>
  `?roT. eval_operand opr t = SOME roT /\
    (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
      w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
      b = w2n roT+(a-w2n ro)) /\
    (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
      ~(w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a b /\
      ~(w2n roT <= b /\ b < w2n roT+LENGTH (TAKE (w2n rs) post.vs_returndata)))` by
    ((
      `?roT. eval_operand opr t = SOME roT /\
        (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
          w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
          w2n roT <= b /\ b < w2n roT+LENGTH (TAKE (w2n rs) post.vs_returndata) /\
          a-w2n ro = b-w2n roT) /\
        (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
          ~(w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
          joint_relocation_demand lo (concretize_positions C') q0 es qs c a b /\
          ~(w2n roT <= b /\ b < w2n roT+LENGTH (TAKE (w2n rs) post.vs_returndata)))` by
        (irule concretize_clean_write_geometry >> simp[] >>
         goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >>
         goal_assum (drule_at (Pat `fn_ptr_ok _ _`)) >>
         goal_assum (drule_at (Pat `lifetime_ok _ _ _`)) >>
         goal_assum (drule_at (Pat `resolved_config_ok _ _ _`)) >>
         goal_assum (drule_at (Pat `callee_first _ _`)) >>
         goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >> simp[] >>
         simp[mem_write_ops_def, codegenRelTheory.source_memory_write_ranges_def,
           memory_range_of_operands_def, step_writes_def, LENGTH_TAKE] >>
         fs[] >> simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]) >>
      qexists_tac `roT` >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!a b. _ ==> _ /\ _ /\ _`
            (qspecl_then [`a`,`b`] mp_tac) >>
          impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
          pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
          pop_assum mp_tac >> pop_assum mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
      qpat_x_assum `!a b. _ /\ ~_ ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      metis_tac[])) >>
  `s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    (fs[relocation_env_def] >> metis_tac[]) >>
  `?post'. exec_ext_call inst t gas addr value offT sz roT rs
      (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) = OK post' /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post'` by
    (irule concretize_ext_call_local_execution >> simp[MEM] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`off`,`ro`] >> fs[] >> fs[] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_x_assum `exec_ext_call inst s _ _ _ _ _ _ _ _ = OK post` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  (conj_tac >- ((
      qpat_x_assum `!op. MEM op _ ==> _` mp_tac >> simp[MEM] >> strip_tac >>
      pure_once_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
      fs[Excl "consume_call_outcome_eq"] >>
      simp[Excl "consume_call_outcome_eq"] >>
      qpat_x_assum `exec_ext_call inst t _ _ _ _ _ _ _ _ = OK post'` mp_tac >>
      asm_rewrite_tac[] >> simp[]))) >>
  (conj_tac >- ((
      `SND o_f rv = G` by
        (drule resolved_config_current >> simp[] >>
         metis_tac[resolved_frame_erasure]) >>
      `inst_wf inst` by
        (fs[o1_fn_shape_def, venomWfTheory.fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
         metis_tac[]) >>
      `?v. inst.inst_outputs = [v]` by
        (qpat_x_assum `inst_wf inst` mp_tac >>
         asm_rewrite_tac[venomWfTheory.inst_wf_def, venomInstTheory.opcode_case_def] >>
         simp[LENGTH_EQ_NUM_compute]) >>
      qpat_x_assum `SND o_f rv = G` (SUBST_ALL_TAC o SYM) >>
      irule ext_call_prov >> simp[] >> metis_tac[]))) >>
  (conj_tac >- ((
      `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
      qpat_assum `exec_ext_call inst s _ _ _ _ _ _ _ _ = OK post`
        (mp_then (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = OK _`) mp_tac
          ext_call_execution_reset_agreement) >>
      disch_then (drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = OK _`)) >>
      simp[MEM] >> disch_then (qspecl_then [`un`, `tn`] strip_assume_tac) >>
      qpat_assum `exec_ext_call inst s _ _ _ _ _ _ _ _ = OK post`
        (mp_then Any strip_assume_tac ext_call_execution_fields) >>
      qpat_assum `exec_ext_call inst t _ _ _ _ _ _ _ _ = OK post'`
        (mp_then Any strip_assume_tac ext_call_execution_fields) >>
      qpat_assum `post.vs_fmp = s.vs_fmp`
        (mp_then (Pat `_ .vs_fmp = _ .vs_fmp`) mp_tac ext_call_taint) >>
      disch_then (drule_at (Pat `_.inst_outputs = [_]`)) >>
      pure_rewrite_tac[APPEND] >>
      disch_then (drule_at (Pat `_.inst_operands = _`)) >>
      disch_then (qspec_then `tn` mp_tac) >>
      (impl_tac >- simp[MEM]) >> disch_tac >>
      qpat_assum `post'.vs_fmp = t.vs_fmp`
        (mp_then (Pat `_ .vs_fmp = _ .vs_fmp`) mp_tac ext_call_taint) >>
      disch_then (drule_at (Pat `_.inst_outputs = [_]`)) >>
      pure_rewrite_tac[APPEND] >>
      disch_then (drule_at (Pat `_.inst_operands = _`)) >>
      disch_then (qspec_then `un` mp_tac) >>
      (impl_tac >- simp[MEM]) >> disch_tac >>
      `(step_taint inst s post tn).t_mem = tn.t_mem DIFF range_bytes (step_writes inst s post) /\
       (step_taint inst s post tn).t_var = tn.t_var |+ (out',{}) /\
       (step_taint inst s post tn).t_imm = tn.t_imm` by simp[] >>
      `(step_taint inst t post' un).t_mem = un.t_mem DIFF range_bytes (step_writes inst t post') /\
       (step_taint inst t post' un).t_var = un.t_var |+ (out',{}) /\
       (step_taint inst t post' un).t_imm = un.t_imm` by simp[] >>
      qpat_x_assum `step_taint inst s post tn = _` kall_tac >>
      qpat_x_assum `step_taint inst t post' un = _` kall_tac >>
      (fs[relocation_taint_le_def] >>
      simp[relocation_taint_le_def] >> conj_tac
      >- (`post.vs_returndata = post'.vs_returndata` by
            (irule local_obs_returndata >> drule local_rel_observation >> simp[]) >>
          `eval_operand opm s = SOME rs` by metis_tac[] >>
          `!op. MEM op vals ==> eval_operand op t = eval_operand op s` by metis_tac[] >>
          simp[step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
               memory_range_of_operands_def, range_bytes_def] >>
          qpat_x_assum `demand_taint _ _ _` mp_tac >>
          qpat_x_assum `!a b. _ ==> b = _` mp_tac >>
          qpat_x_assum `!a b. _ ==> _ /\ _` mp_tac >>
          qpat_x_assum `post.vs_returndata = post'.vs_returndata` mp_tac >>
          rpt (pop_assum kall_tac) >>
          simp[demand_taint_def, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
          qmatch_goalsub_abbrev_tac `w2n ro + len` >> rpt strip_tac >>
          `~(w2n ro <= a /\ a < w2n ro + len)` by
            (strip_tac >>
             qpat_x_assum `!a b. _ ==> b = _`
               (qspecl_then [`a`,`b`] mp_tac) >>
             (impl_tac >- simp[]) >>
             fs[Abbr `len`] >> rpt IF_CASES_TAC >> fs[] >> decide_tac) >>
          qpat_x_assum `!a b. _ ==> _ /\ _`
            (qspecl_then [`a`,`b`] mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          qpat_x_assum `!a b. _ /\ b IN un.t_mem ==> a IN tn.t_mem`
            (qspecl_then [`a`,`b`] mp_tac) >> simp[] >>
          fs[Abbr `len`] >> rpt IF_CASES_TAC >> fs[] >> decide_tac) >>
      conj_tac
      >- (simp[op_taint_def, FLOOKUP_UPDATE] >> gen_tac >>
          IF_CASES_TAC >> simp[] >> fs[op_taint_def]) >>
      Cases_on `reset` >> simp[])))) >>
  ((
      qpat_assum `exec_ext_call inst s _ _ _ _ _ _ _ _ = OK post`
        (mp_then Any strip_assume_tac ext_call_execution_fields) >>
      qpat_assum `exec_ext_call inst t _ _ _ _ _ _ _ _ = OK post'`
        (mp_then Any strip_assume_tac ext_call_execution_fields) >>
      fs[relocation_env_def, relocation_reader_context_def])))
QED

val _ = export_theory();

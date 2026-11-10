Theory lowerDloadPtrResidualInterfaces
Ancestors
  lowerDloadPtrStoreCommon lowerDloadPtrCall venomExecSemantics venomCallOracleDefs venomState
  extCallOracle ptrDiscipline lowerDloadPtrRel lowerDloadPtrMemoryWrite lowerDloadPtrRegion regularCallEmitSim arithmetic list


(* Even with equal payloads and static mode, the request retains the entire
   account and transient stores. Masked equality is not request equality. *)
Theorem dload_call_request_eq_iff:
  read_memory (w2n ao) (w2n az) s =
    read_memory (w2n bo) (w2n bz) t /\
  (st \/ s.vs_call_ctx.cc_static) = (tt \/ t.vs_call_ctx.cc_static) ==>
  (venom_call_request s addr value ao az st =
   venom_call_request t addr value bo bz tt <=>
   s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient)
Proof
  strip_tac >> simp[venom_call_request_def]
QED

Theorem dload_ext_call_success_footprint:
  exec_ext_call inst s gas addr value ao az ro rz st = OK t ==>
  t.vs_requests = record_request
    (venom_call_request s addr value ao az st) s.vs_requests /\
  t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_immutables = s.vs_immutables
Proof
  namedCases_on `inst.inst_outputs` ["", "v vs"]
  >- simp[exec_ext_call_def] >>
  Cases_on `vs` >> simp[exec_ext_call_def, update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dload_computed_precompile_cong:
  rq.cr_kind = rr.cr_kind /\ rq.cr_value = rr.cr_value /\
  rq.cr_target = rr.cr_target /\ rq.cr_data = rr.cr_data ==>
  (computed_precompile rq <=> computed_precompile rr)
Proof
  simp[computed_precompile_def]
QED

Theorem dload_record_request_changed:
  record_request rq xs <> xs <=> ~computed_precompile rq
Proof
  Cases_on `computed_precompile rq` >> simp[record_request_def] >>
  strip_tac >> pop_assum (mp_tac o AP_TERM ``LENGTH:call_request list -> num``) >> simp[]
QED

Theorem dload_take_outcome_observations:
  rq.cr_kind = rr.cr_kind /\ rq.cr_value = rr.cr_value /\
  rq.cr_target = rr.cr_target /\ rq.cr_data = rr.cr_data ==>
  SND (take_outcome rq os) = SND (take_outcome rr os) /\
  (FST (take_outcome rq os)).co_success = (FST (take_outcome rr os)).co_success /\
  (FST (take_outcome rq os)).co_returnData = (FST (take_outcome rr os)).co_returnData /\
  (FST (take_outcome rq os)).co_logs = (FST (take_outcome rr os)).co_logs /\
  (FST (take_outcome rq os)).co_toDelete = (FST (take_outcome rr os)).co_toDelete
Proof
  strip_tac >>
  `computed_precompile rq = computed_precompile rr` by
    (irule dload_computed_precompile_cong >> simp[]) >>
  Cases_on `os` >- simp[take_outcome_def] >>
  Cases_on `computed_precompile rr` >- (
    simp[take_outcome_def] >>
    Cases_on `precompile_result rr.cr_target rr.cr_data` >> simp[] >>
    rename1 `SOME opt` >> Cases_on `opt` >> simp[] >>
    IF_CASES_TAC >> simp[]) >>
  simp[take_outcome_def]
QED

(* Ordinary adoption is distinguished from computed success, which retains
   the request's own stores. This equation is independent of history. *)
Theorem dload_adopt_message_outcome:
  rq.cr_kind = MessageCall ==>
  adopt_outcome rq (FST (take_outcome rq os))
    (rq.cr_accounts,rq.cr_tStorage,logs) =
  if ~rq.cr_static /\ ~computed_precompile rq /\ os <> [] /\
     (HD os).co_success
  then ((HD os).co_accounts,(HD os).co_tStorage,logs ++ (HD os).co_logs)
  else (rq.cr_accounts,rq.cr_tStorage,logs)
Proof
  strip_tac >> Cases_on `computed_precompile rq`
  >- simp[adopt_outcome_computed] >>
  Cases_on `os` >- simp[take_outcome_def, adopt_outcome_def] >>
  simp[take_outcome_def, adopt_outcome_message] >>
  Cases_on `rq.cr_static` >> Cases_on `h.co_success` >> simp[]
QED

Theorem dload_consume_call_adopted:
  consume_call_outcome rq ro rz s = (w,s') ==>
  ((~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
     s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
   (~s.vs_call_ctx.cc_static /\ ~computed_precompile rq /\
     s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success))
Proof
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[] >>
  simp[dload_record_request_changed, take_outcome_rest] >>
  Cases_on `s.vs_outcomes` >> simp[] >>
  `t <> h::t` by
    (strip_tac >> pop_assum (mp_tac o AP_TERM ``LENGTH:call_outcome list -> num``) >> simp[]) >>
  simp[]
QED

Theorem dload_consume_call_store_footprint:
  rq.cr_kind = MessageCall /\ rq.cr_accounts = s.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\
  consume_call_outcome rq ro rz s = (w,s') ==>
  s'.vs_accounts =
    (if ~rq.cr_static /\ ~computed_precompile rq /\ s.vs_outcomes <> [] /\
        (HD s.vs_outcomes).co_success
     then (HD s.vs_outcomes).co_accounts else s.vs_accounts) /\
  s'.vs_transient =
    (if ~rq.cr_static /\ ~computed_precompile rq /\ s.vs_outcomes <> [] /\
        (HD s.vs_outcomes).co_success
     then (HD s.vs_outcomes).co_tStorage else s.vs_transient) /\
  s'.vs_immutables = s.vs_immutables /\
  s'.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
    (s.vs_accounts,s.vs_transient,s.vs_logs) =
   if ~rq.cr_static /\ ~computed_precompile rq /\ s.vs_outcomes <> [] /\
      (HD s.vs_outcomes).co_success
   then ((HD s.vs_outcomes).co_accounts,(HD s.vs_outcomes).co_tStorage,
         s.vs_logs ++ (HD s.vs_outcomes).co_logs)
   else (s.vs_accounts,s.vs_transient,s.vs_logs)` by
    metis_tac[dload_adopt_message_outcome] >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = _` mp_tac >>
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem dload_consume_call_shared_store:
  dload_shared_store tn un s t /\
  rq.cr_kind = MessageCall /\ rr.cr_kind = MessageCall /\
  rq.cr_value = rr.cr_value /\ rq.cr_target = rr.cr_target /\
  rq.cr_data = rr.cr_data /\ rq.cr_static = rr.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rr.cr_accounts = t.vs_accounts /\ rr.cr_tStorage = t.vs_transient /\
  s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome rq ro rz s = (w,s') /\
  consume_call_outcome rr to tz t = (v,t') /\
  (a <=> ~rq.cr_static /\ ~computed_precompile rq /\
         s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success) ==>
  dload_shared_store
    (tn with <|t_stor := if a then {} else tn.t_stor;
               t_trans := if a then {} else tn.t_trans|>)
    (un with <|t_stor := if a then {} else un.t_stor;
               t_trans := if a then {} else un.t_trans|>) s' t'
Proof
  strip_tac >>
  `computed_precompile rq = computed_precompile rr` by
    (irule dload_computed_precompile_cong >> simp[]) >>
  `s'.vs_accounts = (if a then (HD s.vs_outcomes).co_accounts else s.vs_accounts) /\
   s'.vs_transient = (if a then (HD s.vs_outcomes).co_tStorage else s.vs_transient) /\
   s'.vs_immutables = s.vs_immutables /\ s'.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `consume_call_outcome rq ro rz s = (w,s')`
      (mp_then Any mp_tac dload_consume_call_store_footprint) >> simp[]) >>
  `t'.vs_accounts = (if a then (HD s.vs_outcomes).co_accounts else t.vs_accounts) /\
   t'.vs_transient = (if a then (HD s.vs_outcomes).co_tStorage else t.vs_transient) /\
   t'.vs_immutables = t.vs_immutables /\ t'.vs_call_ctx = t.vs_call_ctx` by
    (qpat_assum `consume_call_outcome rr to tz t = (v,t')`
      (mp_then Any mp_tac dload_consume_call_store_footprint) >> simp[]) >>
  Cases_on `a` >>
  gvs[dload_shared_store_def, storage_agree_except_def, word_agree_except_def] >>
  metis_tac[]
QED

(* The flag used by step_taint compares each run against its own history. *)
Theorem dload_consume_call_adopted_cong:
  rq.cr_kind = rr.cr_kind /\ rq.cr_value = rr.cr_value /\
  rq.cr_target = rr.cr_target /\ rq.cr_data = rr.cr_data /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome rq ro rz s = (w,s') /\
  consume_call_outcome rr to tz t = (v,t') ==>
  ((~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
    s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
   (~t.vs_call_ctx.cc_static /\ t'.vs_requests <> t.vs_requests /\
    t'.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success))
Proof
  strip_tac >>
  `computed_precompile rq = computed_precompile rr` by
    (irule dload_computed_precompile_cong >> simp[]) >>
  qpat_assum `consume_call_outcome rq ro rz s = (w,s')`
    (mp_then Any mp_tac dload_consume_call_adopted) >>
  qpat_assum `consume_call_outcome rr to tz t = (v,t')`
    (mp_then Any mp_tac dload_consume_call_adopted) >>
  simp[]
QED

Theorem dload_record_request_changed_cong:
  rq.cr_kind = rr.cr_kind /\ rq.cr_value = rr.cr_value /\
  rq.cr_target = rr.cr_target /\ rq.cr_data = rr.cr_data ==>
  (record_request rq xs <> xs <=> record_request rr ys <> ys)
Proof
  strip_tac >>
  `computed_precompile rq = computed_precompile rr` by
    (irule dload_computed_precompile_cong >> simp[]) >>
  mp_tac dload_record_request_changed >>
  mp_tac (Q.INST [`rq` |-> `rr`, `xs` |-> `ys`] dload_record_request_changed) >>
  simp[]
QED

Theorem dload_consume_call_memory:
  consume_call_outcome rq ro rz s = (w,s') ==>
  s'.vs_memory = (write_memory_with_expansion ro
    (TAKE rz s'.vs_returndata) s).vs_memory
Proof
  simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]
QED

Theorem dload_consume_call_environment:
  dload_equal_environment s t /\
  rq.cr_kind = MessageCall /\ rr.cr_kind = MessageCall /\
  rq.cr_value = rr.cr_value /\ rq.cr_target = rr.cr_target /\
  rq.cr_data = rr.cr_data /\ rq.cr_static = rr.cr_static /\
  consume_call_outcome rq ro rz s = (w,s') /\
  consume_call_outcome rr to tz t = (v,t') ==>
  w = v /\ dload_equal_environment s' t'
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[dload_equal_environment_def, venom_state_component_equality] >>
  `SND (take_outcome rq s.vs_outcomes) = SND (take_outcome rr t.vs_outcomes) /\
   (FST (take_outcome rq s.vs_outcomes)).co_success =
     (FST (take_outcome rr t.vs_outcomes)).co_success /\
   (FST (take_outcome rq s.vs_outcomes)).co_returnData =
     (FST (take_outcome rr t.vs_outcomes)).co_returnData /\
   (FST (take_outcome rq s.vs_outcomes)).co_logs =
     (FST (take_outcome rr t.vs_outcomes)).co_logs /\
   (FST (take_outcome rq s.vs_outcomes)).co_toDelete =
     (FST (take_outcome rr t.vs_outcomes)).co_toDelete` by
    (simp[] >> irule dload_take_outcome_observations >> simp[]) >>
  gvs[consume_call_outcome_eq] >>
  gvs[dload_equal_environment_def, venom_state_component_equality,
      adopt_outcome_def, adopt_outcome_deletions_def]
QED

Theorem dload_write_access_containment:
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  mem_write_ops i = SOME ops /\
  MEM (w2n x,rz) (source_memory_write_ranges i s) ==>
  (rz <> 0 ==> ((lo < w2n x + rz \/ op_prov G ops.iao_ofst <> NONE) ==>
    ?b n. op_prov G ops.iao_ofst = SOME (b,n) /\
      b <= w2n x /\ w2n x + rz <= b+n))
Proof
  rpt strip_tac >>
  `?v b n. ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,n) /\
    b <= w2n x /\ w2n x + rz <= b+n` by
    (fs[access_ok_def] >> metis_tac[]) >>
  gvs[op_prov_def] >> metis_tac[]
QED

Theorem dload_memory_match_memory_cong:
  s1.vs_memory = s2.vs_memory /\ t1.vs_memory = t2.vs_memory ==>
  (dload_memory_match lo fs tn un s1 t1 <=>
   dload_memory_match lo fs tn un s2 t2)
Proof
  simp[dload_memory_match_def]
QED

Theorem dload_clean_return_memory_match:
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\ dload_value_word fs {} p q x y /\
  s'.vs_memory = (write_memory_with_expansion (w2n x)
    (TAKE rz s'.vs_returndata) s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion (w2n y)
    (TAKE rz s'.vs_returndata) t).vs_memory /\
  s'.vs_returndata = t'.vs_returndata /\
  (rz <> 0 ==> ((lo < w2n x + rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n x /\ w2n x + rz <= b+n)) ==>
  dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF
      {a | w2n x <= a /\ a < w2n x + MIN rz (LENGTH s'.vs_returndata)})
    (un with t_mem := un.t_mem DIFF
      {a | w2n y <= a /\ a < w2n y + MIN rz (LENGTH s'.vs_returndata)}) s' t'
Proof
  strip_tac >>
  `LENGTH (TAKE rz s'.vs_returndata) = MIN rz (LENGTH s'.vs_returndata)` by
    (simp[LENGTH_TAKE_EQ, MIN_DEF] >> rw[] >> gvs[] >> decide_tac) >>
  `LENGTH (TAKE rz s'.vs_returndata) <= rz` by simp[] >>
  `MIN rz (LENGTH t'.vs_returndata) <= rz` by simp[] >>
  Cases_on `LENGTH (TAKE rz s'.vs_returndata) = 0`
  >- (fs[LENGTH_TAKE] >>
      fs[dload_memory_match_def, read_byte_write_memory_with_expansion] >>
      metis_tac[]) >>
  `rz <> 0` by (gvs[LENGTH_TAKE] >> decide_tac) >>
  Q.SUBGOAL_THEN
    `((w2n x = w2n y /\ w2n x + rz <= lo) \/
      (?owner id b c n d. dload_live_site fs owner id b c n /\
        w2n x = b+d /\ w2n y = c+d /\ d+rz <= n))` assume_tac
  >- (irule dload_value_contained_region >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `((w2n x = w2n y /\ w2n x + LENGTH (TAKE rz s'.vs_returndata) <= lo) \/
      (?owner id b c n d. dload_live_site fs owner id b c n /\
        w2n x = b+d /\ w2n y = c+d /\
        d+LENGTH (TAKE rz s'.vs_returndata) <= n))` assume_tac
  >- (qpat_x_assum `_ \/ _` strip_assume_tac
      >- (disj1_tac >> conj_tac >- asm_rewrite_tac[] >> decide_tac) >>
      disj2_tac >> qexistsl [`owner`, `id`, `b`, `c`, `n`, `d`] >>
      asm_rewrite_tac[] >> decide_tac) >>
  `dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF
      {a | w2n x <= a /\ a < w2n x + LENGTH (TAKE rz s'.vs_returndata)})
    (un with t_mem := un.t_mem DIFF
      {a | w2n y <= a /\ a < w2n y + LENGTH (TAKE rz s'.vs_returndata)})
    (write_memory_with_expansion (w2n x) (TAKE rz s'.vs_returndata) s)
    (write_memory_with_expansion (w2n y) (TAKE rz s'.vs_returndata) t)` by
    (irule dload_memory_match_clean_write_region >> metis_tac[]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `_ \/ _` kall_tac >>
  gvs[] >> metis_tac[dload_memory_match_memory_cong]
QED

Theorem dload_consume_call_memory_match:
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\ dload_value_word fs {} p q x y /\
  consume_call_outcome rq (w2n x) rz s = (w,s') /\
  consume_call_outcome rr (w2n y) rz t = (v,t') /\
  s'.vs_returndata = t'.vs_returndata /\
  (rz <> 0 ==> ((lo < w2n x + rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n x /\ w2n x + rz <= b+n)) ==>
  dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF
      {a | w2n x <= a /\ a < w2n x + MIN rz (LENGTH s'.vs_returndata)})
    (un with t_mem := un.t_mem DIFF
      {a | w2n y <= a /\ a < w2n y + MIN rz (LENGTH s'.vs_returndata)}) s' t'
Proof
  strip_tac >> irule dload_clean_return_memory_match >>
  metis_tac[dload_consume_call_memory]
QED

Theorem dload_exec_ext_call_environment:
  dload_equal_environment s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n bz) t /\
  exec_ext_call inst t gt addr value bo bz rt rz st = OK t1 ==>
  ?s1. exec_ext_call inst s gs addr value ao az rs rz st = OK s1 /\
    dload_equal_environment s1 t1 /\
    (!out. MEM out inst.inst_outputs ==> lookup_var out s1 = lookup_var out t1) /\
    ((~s.vs_call_ctx.cc_static /\ s1.vs_requests <> s.vs_requests /\
      s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
     (~t.vs_call_ctx.cc_static /\ t1.vs_requests <> t.vs_requests /\
      t1.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success))
Proof
  strip_tac >>
  Cases_on `consume_call_outcome (venom_call_request s addr value ao az st)
    (w2n rs) (w2n rz) s` >>
  rename1 `consume_call_outcome _ _ _ s = (w,ss)` >>
  Cases_on `consume_call_outcome (venom_call_request t addr value bo bz st)
    (w2n rt) (w2n rz) t` >>
  rename1 `consume_call_outcome _ _ _ t = (v,tt)` >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_equal_environment_call_ctx] >>
  `s.vs_outcomes = t.vs_outcomes` by
    metis_tac[dload_equal_environment_outcomes] >>
  `w = v /\ dload_equal_environment ss tt` by
    (irule dload_consume_call_environment >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[venom_call_request_def, dload_equal_environment_call_ctx]) >>
  `((~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
      ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
     (~t.vs_call_ctx.cc_static /\ tt.vs_requests <> t.vs_requests /\
      tt.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success))` by
    (irule dload_consume_call_adopted_cong >>
     goal_assum (drule_at Any) >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[venom_call_request_def]) >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[exec_ext_call_def] >>
  pure_asm_rewrite_tac[LET_THM] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[] >>
  Cases_on `outs` >> simp[] >> strip_tac >>
  qpat_x_assum `consume_call_outcome _ _ _ s = _` kall_tac >>
  qpat_x_assum `consume_call_outcome _ _ _ t = _` kall_tac >>
  qpat_x_assum `update_var _ _ _ = t1` (SUBST_ALL_TAC o SYM) >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_memory_match_update_vars[simp]:
  dload_memory_match lo fs tn un (update_var a x s) (update_var b y t) <=>
  dload_memory_match lo fs tn un s t
Proof
  simp[dload_memory_match_def, update_var_def]
QED

Theorem dload_shared_store_update_vars[simp]:
  dload_shared_store tn un (update_var a x s) (update_var b y t) <=>
  dload_shared_store tn un s t
Proof
  simp[dload_shared_store_def, update_var_def]
QED

Theorem dload_exec_ext_call_memory_match:
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\ dload_value_word fs {} p q rs rt /\
  exec_ext_call inst s gs addr value ao az rs rz st = OK s1 /\
  exec_ext_call inst t gt addr value bo bz rt rz st = OK t1 /\
  s1.vs_returndata = t1.vs_returndata /\
  (w2n rz <> 0 ==> ((lo < w2n rs + w2n rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n rs /\ w2n rs + w2n rz <= b+n)) ==>
  dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF
      {a | w2n rs <= a /\ a < w2n rs + MIN (w2n rz) (LENGTH s1.vs_returndata)})
    (un with t_mem := un.t_mem DIFF
      {a | w2n rt <= a /\ a < w2n rt + MIN (w2n rz) (LENGTH s1.vs_returndata)}) s1 t1
Proof
  strip_tac >>
  Cases_on `consume_call_outcome (venom_call_request s addr value ao az st)
    (w2n rs) (w2n rz) s` >>
  rename1 `consume_call_outcome _ _ _ s = (w,ss)` >>
  Cases_on `consume_call_outcome (venom_call_request t addr value bo bz st)
    (w2n rt) (w2n rz) t` >>
  rename1 `consume_call_outcome _ _ _ t = (v,tt)` >>
  qpat_x_assum `exec_ext_call _ s _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `exec_ext_call _ t _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[exec_ext_call_def] >> pure_asm_rewrite_tac[LET_THM] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >- simp[] >>
  Cases_on `outs` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `update_var _ _ _ = t1` (SUBST_ALL_TAC o SYM) >>
  simpLib.SIMP_TAC (srw_ss()) [dload_memory_match_update_vars, update_var_def] >>
  qpat_assum `_.vs_returndata = _.vs_returndata`
    (fn th => rewrite_tac[GSYM (SRULE[update_var_def] th)]) >>
  irule dload_consume_call_memory_match >> conj_tac
  >- (qpat_x_assum `_.vs_returndata = _.vs_returndata` mp_tac >>
      simp[update_var_def]) >>
  metis_tac[]
QED

Theorem dload_exec_ext_call_shared_store:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n bz) t /\
  exec_ext_call inst s gs addr value ao az rs rz st = OK s1 /\
  exec_ext_call inst t gt addr value bo bz rt rz st = OK t1 /\
  (a <=> ~(st \/ s.vs_call_ctx.cc_static) /\
     ~computed_precompile (venom_call_request s addr value ao az st) /\
     s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success) ==>
  dload_shared_store
    (tn with <|t_stor := if a then {} else tn.t_stor;
               t_trans := if a then {} else tn.t_trans|>)
    (un with <|t_stor := if a then {} else un.t_stor;
               t_trans := if a then {} else un.t_trans|>) s1 t1
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_equal_environment_call_ctx] >>
  `s.vs_outcomes = t.vs_outcomes` by
    metis_tac[dload_equal_environment_outcomes] >>
  Cases_on `consume_call_outcome (venom_call_request s addr value ao az st)
    (w2n rs) (w2n rz) s` >>
  rename1 `consume_call_outcome _ _ _ s = (w,ss)` >>
  Cases_on `consume_call_outcome (venom_call_request t addr value bo bz st)
    (w2n rt) (w2n rz) t` >>
  rename1 `consume_call_outcome _ _ _ t = (v,tt)` >>
  qpat_x_assum `exec_ext_call _ s _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `exec_ext_call _ t _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[exec_ext_call_def] >> pure_asm_rewrite_tac[LET_THM] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >- simp[] >>
  Cases_on `outs` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `update_var _ _ _ = t1` (SUBST_ALL_TAC o SYM) >>
  pure_rewrite_tac[dload_shared_store_update_vars] >>
  irule dload_consume_call_shared_store >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[venom_call_request_def]
QED

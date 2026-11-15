Theory readonlyInvokeCopyFwdStepsDelegate
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdStepsMemory
  readonlyInvokeCopyFwdStepsEffects readonlyInvokeCopyFwdStepsExternalErrors
  readonlyInvokeCopyFwdStepsExternalOracle venomCallOracleDefs
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues o1LowerDloadShared
  o1LowerDloadConcreteExternal o1LowerDloadJointRelation
  taintAgree venomState venomExecSemantics ptrDiscipline
  internalReturnCopyFwdSim finite_map words list pred_set

Theorem ricf_frame_concrete_inputs:
  ricf_frame_agree D X sites PG H tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  ld_joint_local_fields s t /\ s.vs_accounts = t.vs_accounts /\
  s.vs_transient = t.vs_transient /\ s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions
Proof
  strip_tac >>
  `taint_agree D X tn s (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)` by
    fs[ricf_frame_agree_def] >>
  drule_then assume_tac taint_agree_local_fields >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[taint_agree_def, ld_shared_agree_def] >>
  drule_all ld_shared_clean_accounts >>
  drule_all ld_shared_clean_transient >>
  fs[ld_joint_local_fields_def, ld_shared_agree_def]
QED

Theorem ricf_interval_shorten[local]:
  !a n m x:num. m <= n /\ ~(a <= x /\ x < a+n) ==>
    ~(a <= x /\ x < a+m)
Proof
  decide_tac
QED

Theorem ricf_cert_exec_delegatecall:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  un.t_stor = {} /\ un.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
  inst.inst_outputs = [out] /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(w2n ro <= db+k /\ db+k < w2n ro+w2n rz) /\
      ~(w2n ro <= sb+k /\ sb+k < w2n ro+w2n rz)) /\
  exec_delegatecall inst s (gas:256 word) (addr:256 word) ao az ro rz = OK s1 ==>
  ?w r u M. s1 = update_var out w r /\
    exec_delegatecall inst t gas addr ao' az ro rz = OK (update_var out w u) /\
    M = un.t_mem DIFF {i | w2n ro <= i /\
      i < w2n ro + LENGTH (TAKE (w2n rz) r.vs_returndata)} /\
    ricf_cert_core D ids stk PG
      (ricf_effective_prov fn s1 (set_prov H [out] NONE))
      (ricf_effective_taint fn s1
        ((un with t_mem := M) with t_var := set_var_taint un.t_var [out] {})) fn
      sites maps targets (set_prov H [out] NONE)
      ((un with t_mem := M) with t_var := set_var_taint un.t_var [out] {})
      cur curs s1 (update_var out w u)
Proof
  strip_tac >>
  `ld_joint_local_fields s t /\ s.vs_accounts = t.vs_accounts /\
   s.vs_transient = t.vs_transient /\ s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    (irule ricf_frame_concrete_inputs >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[ld_joint_local_fields_def] >>
  `LENGTH maps = LENGTH stk` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_live_stack_agree_def] >>
  qabbrev_tac `rq = venom_call_request s addr 0w ao az F with cr_kind := DelegateMessageCall` >>
  `venom_call_request t addr 0w ao' az F with cr_kind := DelegateMessageCall = rq` by
    simp[Abbr`rq`, venom_call_request_def] >>
  Cases_on `consume_call_outcome rq (w2n ro) (w2n rz) s` >>
  rename1 `consume_call_outcome rq (w2n ro) (w2n rz) s = (w,r)` >>
  Cases_on `consume_call_outcome rq (w2n ro) (w2n rz) t` >>
  rename1 `consume_call_outcome rq (w2n ro) (w2n rz) t = (z,u)` >>
  `s1 = update_var out w r` by
    gvs[exec_delegatecall_def, LET_THM, Abbr`rq`, Excl "consume_call_outcome_eq"] >>
  `!gam. MEM gam (MAP ricf_site_triples maps) ==>
    ?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)` by
    (simp[MEM_MAP, MEM_EL] >> metis_tac[]) >>
  `w = z /\ ricf_cert_core D ids stk PG
    (ricf_effective_prov fn r H)
    (ricf_effective_taint fn r (ricf_call_taint un rq s r (w2n ro) (w2n rz))) fn
    sites maps targets H (ricf_call_taint un rq s r (w2n ro) (w2n rz)) cur curs r u` by
    (irule ricf_cert_consume_call >>
     qpat_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `consume_call_outcome _ _ _ t = _` (irule_at Any) >>
     simp[Abbr`rq`, venom_call_request_def, request_agree_except_def,
       accounts_agree_except_def, transient_agree_except_def,
       storage_agree_except_def, word_agree_except_def, Excl "consume_call_outcome_eq"] >>
     rpt strip_tac >>
     `LENGTH (TAKE (w2n rz) r.vs_returndata) <= w2n rz` by simp[LENGTH_TAKE_EQ] >>
     metis_tac[ricf_interval_shorten, arithmeticTheory.ADD_COMM]) >>
  `ricf_call_taint un rq s r (w2n ro) (w2n rz) = un with t_mem :=
    un.t_mem DIFF {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rz) r.vs_returndata)}` by
    simp[ricf_call_taint_def, taint_component_equality] >>
  qpat_x_assum `ricf_call_taint _ _ _ _ _ _ = _` SUBST_ALL_TAC >>
  qpat_x_assum `w = z` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qexistsl [`w`, `r`, `u`,
    `un.t_mem DIFF {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rz) r.vs_returndata)}`] >>
  simp[exec_delegatecall_def, LET_THM, Abbr`rq`, Excl "consume_call_outcome_eq"] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >>
  goal_assum (drule_at Any) >>
  qexistsl [`{}`, `out`, `NONE`, `w`, `w`] >>
  simp_tac (srw_ss()) [ricf_value_agree_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
    word_agree_except_def, arithmeticTheory.ADD_COMM]
QED

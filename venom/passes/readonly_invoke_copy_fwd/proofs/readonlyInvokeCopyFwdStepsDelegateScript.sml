Theory readonlyInvokeCopyFwdStepsDelegate
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdStepsMemory
  readonlyInvokeCopyFwdStepsEffects readonlyInvokeCopyFwdStepsExternalErrors
  readonlyInvokeCopyFwdStepsExternalOracle venomCallOracleDefs
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues o1LowerDloadShared
  o1LowerDloadConcreteExternal o1LowerDloadJointRelation
  taintAgree venomState venomExecSemantics ptrDiscipline
  internalReturnCopyFwdSim finite_map words list pred_set

(* A concrete result installs common shared observations without touching
   locals or memory.  Memory framing is handled separately by StepsMemory. *)
Theorem ricf_frame_concrete_shared:
  ricf_frame_agree D X sites PG H tn s t ==>
  ricf_frame_agree D X sites PG H tn
    (s with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
      vs_transient := tr; vs_pending_deletions := dels|>)
    (t with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
      vs_transient := tr; vs_pending_deletions := dels|>)
Proof
  simp[ricf_frame_agree_def, taint_agree_def, ld_shared_agree_def,
       word_agree_except_def, op_taint_def, ircf_cross_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM
    `\z. z with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
      vs_transient := tr; vs_pending_deletions := dels|>`) >>
  simp[venom_state_fupdcanon] >> metis_tac[]
QED

Theorem ricf_cert_concrete_shared:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn
      (s with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
        vs_transient := tr; vs_pending_deletions := dels|>) H)
    (ricf_effective_taint fn
      (s with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
        vs_transient := tr; vs_pending_deletions := dels|>) un) fn
    sites maps targets H un cur curs
    (s with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
      vs_transient := tr; vs_pending_deletions := dels|>)
    (t with <|vs_returndata := rd; vs_accounts := ac; vs_logs := logs;
      vs_transient := tr; vs_pending_deletions := dels|>)
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >- (drule ricf_frame_concrete_shared >>
      disch_then (qspecl_then [`tr`, `rd`, `logs`, `dels`, `ac`] mp_tac) >>
      simp[ircf_dead_def]) >>
  fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ricf_frame_concrete_shared >>
  disch_then (qspecl_then [`tr`, `rd`, `logs`, `dels`, `ac`] mp_tac) >>
  simp[merge_callee_state_def]
QED

Theorem ricf_cert_extract_concrete:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  extract_venom_result s value ro rs rr = SOME (w,r) /\
  M = un.t_mem DIFF {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(ro <= db+k /\ db+k < ro+LENGTH (TAKE rs r.vs_returndata)) /\
      ~(ro <= sb+k /\ sb+k < ro+LENGTH (TAKE rs r.vs_returndata))) ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn r H)
    (ricf_effective_taint fn r (un with t_mem := M)) fn
    sites maps targets H (un with t_mem := M) cur curs r
    (t with <|vs_returndata := r.vs_returndata; vs_accounts := r.vs_accounts;
      vs_logs := r.vs_logs; vs_transient := r.vs_transient;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_memory := (write_memory_with_expansion ro (TAKE rs r.vs_returndata) t).vs_memory|>)
Proof
  strip_tac >>
  `ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (write_memory_with_expansion ro (TAKE rs r.vs_returndata) s) H)
    (ricf_effective_taint fn (write_memory_with_expansion ro (TAKE rs r.vs_returndata) s)
      (un with t_mem := M)) fn sites maps targets H (un with t_mem := M) cur curs
    (write_memory_with_expansion ro (TAKE rs r.vs_returndata) s)
    (write_memory_with_expansion ro (TAKE rs r.vs_returndata) t)` by
    (match_mp_tac (ricf_cert_write_memory |> Q.INST
       [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `LENGTH (TAKE rs r.vs_returndata)`]) >>
     simp[] >> rpt strip_tac >>
     `~(ro <= db+k /\ db+k < ro+LENGTH (TAKE rs r.vs_returndata)) /\
      ~(ro <= sb+k /\ sb+k < ro+LENGTH (TAKE rs r.vs_returndata))` by metis_tac[] >>
     gvs[]) >>
  drule ricf_cert_concrete_shared >>
  disch_then (qspecl_then [`r.vs_transient`, `r.vs_returndata`, `r.vs_logs`,
    `r.vs_pending_deletions`, `r.vs_accounts`] mp_tac) >>
  drule_then assume_tac ld_extract_concrete_shape >>
  `write_memory_with_expansion ro (TAKE rs r.vs_returndata) s with
      <|vs_returndata := r.vs_returndata; vs_accounts := r.vs_accounts;
        vs_logs := r.vs_logs; vs_transient := r.vs_transient;
        vs_pending_deletions := r.vs_pending_deletions|> = r` by
    (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
     simp[write_memory_with_expansion_def, write_memory_def, venom_state_fupdcanon]) >>
  qpat_x_assum `_ = r`
    (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [write_memory_with_expansion_def, write_memory_def,
    LET_THM, venom_state_fupdcanon]
QED

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

Theory readonlyInvokeCopyFwdStepsExternalOracle
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdStepsMemory
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdEffects readonlyInvokeCopyFwdValues
  taintAgree venomCallOracleDefs venomState venomExecSemantics
  internalReturnCopyFwdSim ptrDiscipline finite_map words list pred_set

Theorem ricf_consume_create_locals:
  consume_create_outcome rq
    (t with <|vs_vars := vs; vs_params := ps|>) =
  (FST (consume_create_outcome rq t),
   SND (consume_create_outcome rq t) with <|vs_vars := vs; vs_params := ps|>)
Proof
  simp[consume_create_outcome_eq]
QED

Theorem ricf_frame_consume_create:
  ricf_frame_agree D X sites PG H tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  consume_create_outcome rq s = (w,r) /\
  consume_create_outcome rq t = (z,u) ==>
  w = z /\ ricf_frame_agree D X sites PG H tn r u
Proof
  strip_tac >>
  `taint_agree D X tn s
     (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)` by
    fs[ricf_frame_agree_def] >>
  drule_all taint_agree_consume_create >> strip_tac >>
  gvs[ricf_consume_create_locals, Excl "consume_create_outcome_eq"] >>
  qpat_x_assum `consume_create_outcome rq s = _` mp_tac >>
  qpat_x_assum `consume_create_outcome rq t = _` mp_tac >>
  simp[consume_create_outcome_eq, pairTheory.PAIR_EQ] >>
  rpt strip_tac >> gvs[] >>
  fs[ricf_frame_agree_def, ircf_cross_def, op_taint_def] >> gvs[]
QED

Theorem ricf_consume_create_merge:
  consume_create_outcome rq (merge_callee_state a s) =
  (FST (consume_create_outcome rq s),
   merge_callee_state a (SND (consume_create_outcome rq s)))
Proof
  simp[consume_create_outcome_eq, merge_callee_state_def]
QED

Theorem ricf_cert_consume_create:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  un.t_stor = {} /\ un.t_trans = {} /\
  consume_create_outcome rq s = (w,r) /\
  consume_create_outcome rq t = (z,u) ==>
  w = z /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn r H) (ricf_effective_taint fn r un) fn
    sites maps targets H un cur curs r u
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  `w = z /\ ricf_frame_agree D (ircf_dead ids s stk) sites
      (ricf_complete_params PG s.vs_params) H un r u` by
    metis_tac[ricf_frame_consume_create] >> simp[] >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[consume_create_outcome_eq, pairTheory.PAIR_EQ, ircf_cross_def] >> metis_tac[])
  >- (gvs[consume_create_outcome_eq, pairTheory.PAIR_EQ,
          ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >- (gvs[consume_create_outcome_eq, pairTheory.PAIR_EQ, ircf_dead_def]) >>
  fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  drule ricf_frame_consume_create >>
  disch_then (qspecl_then [`z`, `w`, `merge_callee_state (EL j targets) u`,
    `rq`, `merge_callee_state (EL j stk).cf_state r`] mp_tac) >>
  simp[ricf_consume_create_merge, consume_create_outcome_eq]
QED

Theorem ricf_create_request_agree:
  ricf_frame_agree D X sites PG H tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t ==>
  venom_create_request s value off sz salt =
    venom_create_request t value off' sz salt
Proof
  strip_tac >> irule venom_create_request_eq_from_slice >> simp[] >>
  fs[ricf_frame_agree_def] >> drule taint_agree_shared >>
  strip_tac >>
  drule_all o1LowerDloadConcreteExternalTheory.ld_shared_clean_accounts >>
  drule_all o1LowerDloadConcreteExternalTheory.ld_shared_clean_transient >> simp[]
QED

Theorem ricf_cert_exec_create:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  un.t_stor = {} /\ un.t_trans = {} /\ inst.inst_outputs = [out] /\
  w2n sz <= 2 * max_code_size /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t ==>
  ?w r u. exec_create inst s value off sz salt = OK (update_var out w r) /\
    exec_create inst t value off' sz salt = OK (update_var out w u) /\
    ricf_cert_core D ids stk PG
      (ricf_effective_prov fn (update_var out w r) (set_prov H [out] NONE))
      (ricf_effective_taint fn (update_var out w r)
        (un with t_var := set_var_taint un.t_var [out] {})) fn
      sites maps targets (set_prov H [out] NONE)
      (un with t_var := set_var_taint un.t_var [out] {}) cur curs
      (update_var out w r) (update_var out w u)
Proof
  strip_tac >>
  `venom_create_request s value off sz salt =
     venom_create_request t value off' sz salt` by
    (irule ricf_create_request_agree >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def] >> metis_tac[]) >>
  Cases_on `consume_create_outcome (venom_create_request s value off sz salt) s` >>
  Cases_on `consume_create_outcome (venom_create_request s value off sz salt) t` >>
  drule_all ricf_cert_consume_create >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  qexistsl [`q`, `r`, `r'`] >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >>
  `ricf_value_agree sites NONE {} q q` by
    simp[ricf_value_agree_inactive, word_agree_except_def] >> metis_tac[]
QED

(* Return data overwrites only the actual truncated byte string. *)
Definition ricf_call_taint_def:
  ricf_call_taint tn rq s r ro rs =
    tn with <|t_mem := tn.t_mem DIFF
      {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)};
      t_stor := if ~rq.cr_static /\ r.vs_requests <> s.vs_requests /\
        r.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
        then {} else tn.t_stor;
      t_trans := if ~rq.cr_static /\ r.vs_requests <> s.vs_requests /\
        r.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
        then {} else tn.t_trans|>
End

Theorem ricf_consume_call_locals:
  consume_call_outcome rq ro rs
    (t with <|vs_vars := vs; vs_params := ps|>) =
  (FST (consume_call_outcome rq ro rs t),
   SND (consume_call_outcome rq ro rs t) with <|vs_vars := vs; vs_params := ps|>)
Proof
  simp[consume_call_outcome_eq, write_memory_with_expansion_def, write_memory_def]
QED

Theorem ricf_consume_call_merge:
  consume_call_outcome rq ro rs (merge_callee_state a s) =
  (FST (consume_call_outcome rq ro rs s),
   merge_callee_state a (SND (consume_call_outcome rq ro rs s)))
Proof
  simp[consume_call_outcome_eq, merge_callee_state_def,
       write_memory_with_expansion_def, write_memory_def]
QED

Theorem ricf_consume_call_footprint:
  consume_call_outcome rq ro rs s = (w,r) ==>
  r.vs_vars = s.vs_vars /\ r.vs_params = s.vs_params /\
  r.vs_allocas = s.vs_allocas /\
  (!i. ~(ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)) ==>
    read_byte i r.vs_memory = read_byte i s.vs_memory)
Proof
  simp[consume_call_outcome_eq, pairTheory.PAIR_EQ] >>
  rpt strip_tac >> gvs[] >>
  simp[regularCallEmitSimTheory.read_byte_write_memory_with_expansion]
QED

Theorem ricf_frame_consume_call:
  ricf_frame_agree D X sites PG H tn s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro rs s = (w,r) /\
  consume_call_outcome rq2 ro rs t = (z,u) /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE rs r.vs_returndata))) ==>
  w = z /\ ricf_frame_agree D X sites PG H
    (ricf_call_taint tn rq1 s r ro rs) r u
Proof
  strip_tac >>
  `taint_agree D X tn s
    (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)` by
    fs[ricf_frame_agree_def] >>
  `consume_call_outcome rq2 ro rs
     (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>) =
     (z,u with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)` by
    simp[ricf_consume_call_locals, Excl "consume_call_outcome_eq"] >>
  `rq2.cr_accounts =
     (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>).vs_accounts /\
   rq2.cr_tStorage =
     (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>).vs_transient` by simp[] >>
  `((computed_precompile rq1 /\ computed_precompile rq2 /\
     rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
     request_agree_except D rq1 rq2)` by metis_tac[] >>
  drule_all taint_agree_consume_call >> strip_tac >>
  drule_all ricf_consume_call_footprint >> strip_tac >>
  `r.vs_returndata = u.vs_returndata` by
    (gvs[taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_def,
         Excl "consume_call_outcome_eq"]) >>
  `!i. ~(ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)) ==>
     read_byte i u.vs_memory = read_byte i t.vs_memory` by
    metis_tac[ricf_consume_call_footprint] >>
  simp[ricf_frame_agree_def, ricf_call_taint_def, op_taint_def,
       Excl "consume_call_outcome_eq"] >>
  fs[ricf_frame_agree_def, Excl "consume_call_outcome_eq"] >>
  reverse conj_tac
  >- (fs[ircf_cross_def, ricf_call_taint_def,
         Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  gvs[Excl "consume_call_outcome_eq"]
QED

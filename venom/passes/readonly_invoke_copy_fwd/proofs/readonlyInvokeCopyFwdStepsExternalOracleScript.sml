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
  drule taint_agree_consume_call >>
  disch_then (drule_at (Pat `consume_call_outcome _ _ _ s = _`)) >>
  disch_then (drule_at (Pat `consume_call_outcome _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  qpat_assum `consume_call_outcome rq1 ro rs s = _`
    (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
  qpat_assum `consume_call_outcome rq2 ro rs t = _`
    (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
  `r.vs_returndata = u.vs_returndata` by
    (drule taint_agree_read_fields >> simp[] >>
     drule taint_agree_read_fields >> simp[]) >>
  `!i. ~(ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)) ==>
     read_byte i u.vs_memory = read_byte i t.vs_memory` by
    metis_tac[ricf_consume_call_footprint] >>
  simp[ricf_frame_agree_def, ricf_call_taint_def, op_taint_def,
       Excl "consume_call_outcome_eq"] >>
  fs[ricf_frame_agree_def, Excl "consume_call_outcome_eq"] >>
  gvs[op_taint_def, Excl "consume_call_outcome_eq"] >>
  fs[ircf_cross_def, ricf_call_taint_def, Excl "consume_call_outcome_eq"] >>
  metis_tac[]
QED

Theorem ricf_cross_consume_call:
  ircf_cross tn gam s t /\
  consume_call_outcome rq1 ro rs s = (w,r) /\
  consume_call_outcome rq2 ro rs t = (z,u) /\
  r.vs_returndata = u.vs_returndata /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
    ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE rs r.vs_returndata))) ==>
  ircf_cross (ricf_call_taint tn rq1 s r ro rs) gam r u
Proof
  strip_tac >>
  qpat_assum `consume_call_outcome rq1 ro rs s = _`
    (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
  qpat_assum `consume_call_outcome rq2 ro rs t = _`
    (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
  fs[ircf_cross_def, ricf_call_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_consume_call:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro rs s = (w,r) /\
  consume_call_outcome rq2 ro rs t = (z,u) /\
  (!gam db sb sz k.
    (gam = ricf_site_triples sites \/ MEM gam (MAP ricf_site_triples maps) \/
     gam = cur \/ MEM gam curs) /\ (db,sb,sz) IN gam /\ k < sz ==>
    ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE rs r.vs_returndata))) ==>
  w = z /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn r H)
    (ricf_effective_taint fn r (ricf_call_taint un rq1 s r ro rs)) fn
    sites maps targets H (ricf_call_taint un rq1 s r ro rs) cur curs r u
Proof
  strip_tac >> (
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  `w = z /\ ricf_frame_agree D (ircf_dead ids s stk) sites
      (ricf_complete_params PG s.vs_params) H
      (ricf_call_taint un rq1 s r ro rs) r u` by
    (irule ricf_frame_consume_call >> metis_tac[]) >> simp[] >>
  `r.vs_returndata = u.vs_returndata` by
    (fs[ricf_frame_agree_def] >> drule taint_agree_read_fields >> simp[]) >>
  qpat_assum `consume_call_outcome rq1 ro rs s = _`
    (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (irule ricf_cross_consume_call >> metis_tac[])
  >- (fs[ricf_cert_crosses_def, EVERY_MEM, Excl "consume_call_outcome_eq"] >> rpt strip_tac >>
      irule ricf_cross_consume_call >> metis_tac[arithmeticTheory.ADD_COMM])
  >- gvs[ircf_dead_def, Excl "consume_call_outcome_eq"] >>
  fs[ricf_live_stack_agree_def, Excl "consume_call_outcome_eq"] >> rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _`
    (qspec_then `j` mp_tac) >> simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
  drule ricf_frame_consume_call >>
  disch_then (qspecl_then [`z`, `w`, `merge_callee_state (EL j targets) u`,
    `rs`, `rq2`, `rq1`, `ro`, `merge_callee_state (EL j stk).cf_state r`] mp_tac) >>
  simp[ricf_consume_call_merge, merge_callee_state_def,
       ricf_call_taint_def, Excl "consume_call_outcome_eq"] >>
  impl_tac >- (
    `MEM (ricf_site_triples (EL j maps)) (MAP ricf_site_triples maps)` by
      (simp[MEM_MAP] >> qexists_tac `EL j maps` >> simp[MEM_EL] >> metis_tac[]) >>
    metis_tac[]) >>
  simp[])
QED

Theorem ricf_call_request_compatible:
  ricf_frame_agree D X sites PG H tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
  (computed_precompile (venom_call_request s addr value ao az static) \/
   (accounts_agree_except D s.vs_accounts t.vs_accounts /\
    transient_agree_except D s.vs_transient t.vs_transient)) ==>
  ((computed_precompile (venom_call_request s addr value ao az static) /\
    computed_precompile (venom_call_request t addr value ao' az static) /\
    (venom_call_request s addr value ao az static).cr_target =
      (venom_call_request t addr value ao' az static).cr_target /\
    (venom_call_request s addr value ao az static).cr_data =
      (venom_call_request t addr value ao' az static).cr_data) \/
   request_agree_except D (venom_call_request s addr value ao az static)
     (venom_call_request t addr value ao' az static))
Proof
  rpt gen_tac >> disch_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (fs[ricf_frame_agree_def] >> drule taint_agree_call_ctx >> simp[]) >>
  fs[Excl "consume_call_outcome_eq"]
  >- (disj1_tac >> gvs[extCallOracleTheory.computed_precompile_def, venom_call_request_def]) >>
  disj2_tac >> irule o1LowerDloadJointExternalTheory.ld_venom_call_request_masked >> simp[]
QED

Theorem ricf_cert_exec_ext_call:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_outputs = [out] /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
  (computed_precompile (venom_call_request s addr value ao az static) \/
   (accounts_agree_except D s.vs_accounts t.vs_accounts /\
    transient_agree_except D s.vs_transient t.vs_transient)) /\
  consume_call_outcome (venom_call_request s addr value ao az static)
    (w2n ro) (w2n rs) s = (w,r) /\
  (!gam db sb sz k.
    (gam = ricf_site_triples sites \/ MEM gam (MAP ricf_site_triples maps) \/
     gam = cur \/ MEM gam curs) /\ (db,sb,sz) IN gam /\ k < sz ==>
    ~(w2n ro <= db+k /\ db+k < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)) /\
    ~(w2n ro <= sb+k /\ sb+k < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata))) ==>
  ?u. exec_ext_call inst s gas addr value ao az ro rs static = OK (update_var out w r) /\
    exec_ext_call inst t gas addr value ao' az ro rs static = OK (update_var out w u) /\
    ricf_cert_core D ids stk PG
      (ricf_effective_prov fn (update_var out w r) (set_prov H [out] NONE))
      (ricf_effective_taint fn (update_var out w r)
        (ricf_call_taint un (venom_call_request s addr value ao az static) s r
          (w2n ro) (w2n rs) with t_var := set_var_taint un.t_var [out] {})) fn
      sites maps targets (set_prov H [out] NONE)
      (ricf_call_taint un (venom_call_request s addr value ao az static) s r
        (w2n ro) (w2n rs) with t_var := set_var_taint un.t_var [out] {}) cur curs
      (update_var out w r) (update_var out w u)
Proof
  strip_tac >> (
  `((computed_precompile (venom_call_request s addr value ao az static) /\
    computed_precompile (venom_call_request t addr value ao' az static) /\
    (venom_call_request s addr value ao az static).cr_target =
      (venom_call_request t addr value ao' az static).cr_target /\
    (venom_call_request s addr value ao az static).cr_data =
      (venom_call_request t addr value ao' az static).cr_data) \/
   request_agree_except D (venom_call_request s addr value ao az static)
     (venom_call_request t addr value ao' az static))` by
    (irule ricf_call_request_compatible >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def, Excl "consume_call_outcome_eq"] >>
     metis_tac[]) >>
  Cases_on `consume_call_outcome (venom_call_request t addr value ao' az static)
    (w2n ro) (w2n rs) t` >>
  `w = q /\ ricf_cert_core D ids stk PG
    (ricf_effective_prov fn r H)
    (ricf_effective_taint fn r
      (ricf_call_taint un (venom_call_request s addr value ao az static) s r (w2n ro) (w2n rs))) fn
    sites maps targets H
      (ricf_call_taint un (venom_call_request s addr value ao az static) s r (w2n ro) (w2n rs))
    cur curs r r'` by
    (irule ricf_cert_consume_call >>
     qpat_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `consume_call_outcome _ _ _ t = _` (irule_at Any) >>
     simp[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
     fs[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `r'` >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  irule ricf_cert_bind >>
  qpat_assum `ricf_cert_core _ _ _ _ (ricf_effective_prov _ _ _) _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def, ricf_call_taint_def] >>
  `ricf_value_agree sites NONE {} w w` by
    simp[ricf_value_agree_inactive, word_agree_except_def] >> metis_tac[])
QED

(* Dispatch equations keep the certificate results independent of operand syntax. *)
Theorem ricf_dispatch_call:
  inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rs] /\
  eval_operand g s = SOME gas /\ eval_operand a s = SOME addr /\
  eval_operand v s = SOME value /\ eval_operand ao s = SOME off /\
  eval_operand az s = SOME sz /\ eval_operand ro s = SOME ret /\
  eval_operand rs s = SOME len /\ (~s.vs_call_ctx.cc_static \/ value = 0w) ==>
  step_inst fuel C inst s = exec_ext_call inst s gas addr value off sz ret len s.vs_call_ctx.cc_static
Proof
  strip_tac >> simp[venomExecSemanticsTheory.step_inst_non_invoke,
    step_inst_base_def]
QED

Theorem ricf_dispatch_staticcall:
  inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rs] /\
  eval_operand g s = SOME gas /\ eval_operand a s = SOME addr /\
  eval_operand ao s = SOME off /\ eval_operand az s = SOME sz /\
  eval_operand ro s = SOME ret /\ eval_operand rs s = SOME len ==>
  step_inst fuel C inst s = exec_ext_call inst s gas addr 0w off sz ret len T
Proof
  strip_tac >> simp[venomExecSemanticsTheory.step_inst_non_invoke,
    step_inst_base_def]
QED

Theorem ricf_dispatch_create:
  inst.inst_opcode = CREATE /\ inst.inst_operands = [v;ao;az] /\
  eval_operand v s = SOME value /\ eval_operand ao s = SOME off /\
  eval_operand az s = SOME sz /\ ~s.vs_call_ctx.cc_static ==>
  step_inst fuel C inst s = exec_create inst s value off sz NONE
Proof
  strip_tac >> simp[venomExecSemanticsTheory.step_inst_non_invoke,
    step_inst_base_def]
QED

Theorem ricf_dispatch_create2:
  inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v;ao;az;sa] /\
  eval_operand v s = SOME value /\ eval_operand ao s = SOME off /\
  eval_operand az s = SOME sz /\ eval_operand sa s = SOME salt /\
  ~s.vs_call_ctx.cc_static ==>
  step_inst fuel C inst s = exec_create inst s value off sz (SOME salt)
Proof
  strip_tac >> simp[venomExecSemanticsTheory.step_inst_non_invoke,
    step_inst_base_def]
QED

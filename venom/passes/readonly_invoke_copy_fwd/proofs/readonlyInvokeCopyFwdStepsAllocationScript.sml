Theory readonlyInvokeCopyFwdStepsAllocation
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdRel
  taintAgree o1LowerDloadShared ptrDiscipline venomState venomExecSemantics
  internalReturnCopyFwdSim finite_map words list pred_set

Theorem ricf_frame_alloca_fresh:
  ricf_frame_agree D X sites PG G tn s t /\
  X SUBSET Y /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next) ==>
  ricf_frame_agree D Y sites PG G
    (tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z})
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,z));
              vs_alloca_next := s.vs_alloca_next+z|>)
    (t with <|vs_allocas := t.vs_allocas |+ (id,(t.vs_alloca_next,z));
              vs_alloca_next := t.vs_alloca_next+z|>)
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    (fs[ricf_frame_agree_def] >> drule taint_agree_allocation_fields >> simp[]) >>
  `taint_agree D Y tn s
    (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)` by
    (irule taint_agree_hidden_mono >> fs[ricf_frame_agree_def] >> metis_tac[]) >>
  drule taint_agree_alloca_fresh >> simp[] >>
  disch_then (qspecl_then [`z`, `id`] assume_tac) >>
  fs[ricf_frame_agree_def, op_taint_def] >> simp[] >>
  fs[ircf_cross_def] >> rpt strip_tac >>
  qpat_assum `!db sb sz k. _ ==> _ < t.vs_alloca_next /\ _`
    (qspecl_then [`db`, `sb`, `sz`, `k`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> strip_tac >> simp[] >>
  qpat_x_assum `!db sb sz k. _ ==> (_ IN tn.t_mem <=> _) /\ _`
    (qspecl_then [`db`, `sb`, `sz`, `k`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem ricf_cross_alloca_fresh:
  ircf_cross tn gam s t /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==> db+k < a /\ sb+k < a) ==>
  ircf_cross (tn with t_mem := tn.t_mem UNION {i | a <= i /\ i < a+z}) gam
    (s with <|vs_allocas := A; vs_alloca_next := n|>)
    (t with <|vs_allocas := B; vs_alloca_next := m|>)
Proof
  simp[ircf_cross_def] >> rpt strip_tac >>
  qpat_assum `!db sb sz k. _ ==> _ < a /\ _`
    (qspecl_then [`db`, `sb`, `sz`, `k`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> strip_tac >> simp[] >>
  qpat_x_assum `!db sb sz k. _ ==> (_ IN tn.t_mem <=> _) /\ _`
    (qspecl_then [`db`, `sb`, `sz`, `k`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem ricf_cert_alloca_fresh_frame:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  FLOOKUP s.vs_allocas id = NONE /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next) /\
  u = s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,z));
                vs_alloca_next := s.vs_alloca_next+z|> /\
  v = t with <|vs_allocas := t.vs_allocas |+ (id,(t.vs_alloca_next,z));
                vs_alloca_next := t.vs_alloca_next+z|> /\
  un = tn0 with t_mem := tn0.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z} ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn u G0) (ricf_effective_taint fn u un) fn
    sites maps targets G0 un cur curs u v
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> conj_tac
  >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule ricf_cross_alloca_fresh >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (fs[ricf_cert_crosses_def] >> simp[ricf_cert_crosses_def, EVERY_MEM] >>
      rpt strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule ricf_cross_alloca_fresh >> fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (simp[ricf_complete_params_def] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      match_mp_tac (Q.INST [`X` |-> `ircf_dead ids s stk`] ricf_frame_alloca_fresh) >>
      conj_tac >- metis_tac[ricf_complete_params_def] >> conj_tac
      >- (irule ircf_dead_allocas_mono >> simp[SUBMAP_FUPDATE_FLOOKUP]) >>
      qpat_x_assum `!gam. _` (qspec_then `ricf_site_triples sites` mp_tac) >>
      simp[]) >>
  fs[ricf_live_stack_agree_def, ricf_live_frame_decompose] >>
  simp[ricf_live_stack_agree_def, ricf_live_frame_decompose] >>
  qx_gen_tac `j` >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  fs[ld_shared_agree_def] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> irule ricf_cross_alloca_fresh >>
  conj_tac
  >- (qpat_x_assum `!gam. _` (qspec_then `ricf_site_triples (EL j maps)` mp_tac) >>
      simp[] >> metis_tac[]) >> simp[]
QED

(* Equality-eliminating interface to Core's binding rule. *)
Theorem ricf_cert_bind_result:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_value_agree sites p m x y ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out x s) (set_prov G0 [out] p))
    (ricf_effective_taint fn (update_var out x s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn
    sites maps targets (set_prov G0 [out] p)
    (tn0 with t_var := set_var_taint tn0.t_var [out] m) cur curs
    (update_var out x s) (update_var out y t)
Proof
  strip_tac >> drule ricf_cert_bind >>
  disch_then match_mp_tac >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

(* ALLOCA returns a local root, not an inherited relocated parameter. *)
Theorem ricf_cert_alloca_cached:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) /\
  (b,z) NOTIN FDOM sites ==>
  step_inst_base inst s = OK (update_var out (n2w b) s) /\
  step_inst_base inst t = OK (update_var out (n2w b) t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (n2w b) s) (set_prov G0 [out] (SOME (b,z))))
    (ricf_effective_taint fn (update_var out (n2w b) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] {})) fn
    sites maps targets (set_prov G0 [out] (SOME (b,z)))
    (tn0 with t_var := set_var_taint tn0.t_var [out] {}) cur curs
    (update_var out (n2w b) s) (update_var out (n2w b) t)
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def] >>
     drule taint_agree_allocation_fields >> simp[]) >>
  gvs[] >> simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  irule ricf_cert_bind_result >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def,
       ricf_value_agree_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
       word_agree_except_def] >> metis_tac[]
QED

Theorem ricf_cert_alloca_fresh:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  (s.vs_alloca_next,w2n amount) NOTIN FDOM sites /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next) /\
  u = s with <|vs_allocas := s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,w2n amount));
                vs_alloca_next := s.vs_alloca_next+w2n amount|> /\
  v = t with <|vs_allocas := t.vs_allocas |+ (inst.inst_id,(t.vs_alloca_next,w2n amount));
                vs_alloca_next := t.vs_alloca_next+w2n amount|> /\
  un = tn0 with t_mem := tn0.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount} ==>
  step_inst_base inst s = OK (update_var out (n2w s.vs_alloca_next) u) /\
  step_inst_base inst t = OK (update_var out (n2w s.vs_alloca_next) v) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (n2w s.vs_alloca_next) u)
      (set_prov G0 [out] (SOME (s.vs_alloca_next,w2n amount))))
    (ricf_effective_taint fn (update_var out (n2w s.vs_alloca_next) u)
      (un with t_var := set_var_taint un.t_var [out] {})) fn
    sites maps targets (set_prov G0 [out] (SOME (s.vs_alloca_next,w2n amount)))
    (un with t_var := set_var_taint un.t_var [out] {}) cur curs
    (update_var out (n2w s.vs_alloca_next) u)
    (update_var out (n2w s.vs_alloca_next) v)
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def] >>
     drule taint_agree_allocation_fields >> simp[]) >>
  `ricf_cert_core D ids stk PG (ricf_effective_prov fn u G0)
     (ricf_effective_taint fn u un) fn sites maps targets G0 un cur curs u v` by
    (drule_all ricf_cert_alloca_fresh_frame >> simp[]) >>
  conj_tac >- simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  conj_tac >- gvs[step_inst_base_opcode_eqs, exec_alloca_def] >>
  irule ricf_cert_bind_result >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def,
       ricf_value_agree_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
       word_agree_except_def] >> metis_tac[]
QED

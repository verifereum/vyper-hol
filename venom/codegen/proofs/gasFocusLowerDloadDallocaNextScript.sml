(* Resume the actual successful LowerDload body after a dynamic allocation. *)
Theory gasFocusLowerDloadDallocaNext
Ancestors
  o1SafeUpto gasCount lowerDloadOrdinaryEndpoint
  lowerDloadSafetyAdvance lowerDloadReturnOrdinary lowerDloadReturnAlignment
  lowerDloadSafetyAmbient
  lowerDloadSafetyLocations lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadOracleCallAssembly contextCodegenRel
  ptrDiscipline ptrDisciplineEmptyTaint o1PassContract
  venomExecProps venomExecSemantics venomInst list rich_list arithmetic words
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_dalloca_body_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  inst.inst_opcode = DALLOCA /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ step_inst fuel C' inst t = OK u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  ?ss g i Y.
    step_inst 0 C inst s = OK ss /\ g.lf_fn = fn /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx) /\ ld_image g = ld_image f /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (u with vs_inst_idx := SUC t.vs_inst_idx) A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs) /\
    ld_envelope g.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx) /\
    ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0
      (u with vs_inst_idx := SUC t.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb /\
    0 < LENGTH Y /\ get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y) /\
    ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    ss.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs s` by
    (qpat_x_assum `gas_cut n vs q` mp_tac >> simp[Abbr`q`, gas_cut_def] >> decide_tac) >>
  `ctx_has_dalloca C` by
    (drule ld_frame_reachable_certificate >> simp[] >> strip_tac >>
     simp[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[ld_active_inst_member]) >>
  `taint_ok fn tn inst s /\ allocas_below_fmp s` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  `w2n vs.vs_initial_fmp <= w2n s.vs_fmp` by
    (drule frame_reachable_initial_fmp >> simp[allocas_below_fmp_def] >>
     metis_tac[allocas_below_fmp_def]) >>
  drule_all ld_sync_dalloca_effect_at >> strip_tac >>
  suspend "advance"
QED

Resume ld_focus_dalloca_body_next[advance]:
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by simp[is_terminator_def] >>
  `step_inst 0 C inst s = OK ss` by fs[step_inst_non_invoke] >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `q.vs_current_bb = t.vs_current_bb /\ q.vs_inst_idx = SUC p` by simp[Abbr`q`] >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists_tac `bb` >> fs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  qabbrev_tac `ss1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  `?i Y. active_inst fn i ss1 /\ ld_envelope f.lf_supply fn ss1 (SUC s.vs_inst_idx) Y (SUC p) /\
          0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1, Abbr`ss1`]) >>
  qabbrev_tac `g = f with <|lf_src := ss1; lf_tgt := q; lf_H := H';
                            lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr`g`, Abbr`ss1`, Abbr`q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn i ss1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[]) >>
  suspend "package"
QED

Resume ld_focus_dalloca_body_next[package]:
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
   g.lf_Q = f.lf_Q /\ g.lf_supply = f.lf_supply /\
   g.lf_src = ss1 /\ g.lf_tgt = q` by simp[Abbr`g`] >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (qpat_assum `fs0 = fs` SUBST_ALL_TAC >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >> metis_tac[]) >>
  `ld_return_cont C fn cs ss1` by
    (simp[Abbr`ss1`] >> irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[]) >>
  `ld_image g = ld_image f` by simp[ld_image_def] >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs` by
    (qpat_x_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     simp[EVERY_MEM] >> strip_tac >> qx_gen_tac `a` >> disch_tac >>
     qpat_assum `!a. MEM a fs ==> _` (qspec_then `a` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `LENGTH u.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings` by
       (irule LESS_EQ_TRANS >> qexists_tac `LENGTH t.vs_gas_readings` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0 q q` by
    (pure_rewrite_tac[ld_prefix_zero, REFL_CLAUSE, AND_CLAUSES] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >>
     qpat_assum `j = EL 0 Y` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y)` by
    (qpat_assum `t.vs_inst_idx = p` SUBST1_TAC >>
     qpat_assum `q.vs_inst_idx = SUC p` (SUBST1_TAC o SYM) >>
     qpat_assum `j = EL 0 Y` (SUBST1_TAC o SYM o PURE_REWRITE_RULE [CONJUNCT1 EL]) >>
     first_assum ACCEPT_TAC) >>
  `lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb` by
    (qpat_assum `u.vs_current_bb = t.vs_current_bb` SUBST1_TAC >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `g.lf_src.vs_gas_readings = ss.vs_gas_readings /\
   g.lf_tgt.vs_gas_readings = u.vs_gas_readings` by simp[Abbr`ss1`, Abbr`q`] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by simp[] >>
  `ld_envelope g.lf_supply fn ss1 (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >>
     qpat_assum `t.vs_inst_idx = p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ss`,`g`,`i`,`Y`] >>
  qpat_assum `Abbrev (ss1 = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (q = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_assum `g.lf_fn = f.lf_fn` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qpat_x_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)`
       (strip_assume_tac o SRULE [] o BETA_RULE) >>
     `!a. MEM a fs ==> !v. MEM (SOME v) a.lf_Q ==> v IN ld_slots A fs` by
       (qpat_assum `!a. MEM a fs0 ==> FRANGE a.lf_H SUBSET ld_slots A fs0 /\ _` mp_tac >>
        qpat_assum `fs0 = fs` SUBST1_TAC >> metis_tac[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `t.vs_inst_idx = p` (SUBST1_TAC o SYM) >>
  qpat_assum `u.vs_current_bb = t.vs_current_bb` (SUBST1_TAC o SYM) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise ld_focus_dalloca_body_next

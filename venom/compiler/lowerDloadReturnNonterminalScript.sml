(* Successful-return reconstruction at completed nonterminal expansions. *)
Theory lowerDloadReturnNonterminal
Ancestors
  lowerDloadReturnStable lowerDloadFullEndpoint lowerDloadReturnAlignment
  lowerDloadEnvelopeControl
  venomExecProofs list venomWf venomInst passSharedDefs o1PassContract
  venomExecSemantics arithmetic contextCodegenRel
Libs
  lowerDloadReturnPackageLib

Theorem ld_return_point_endpoint_next:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  fn' = ld_image f /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  ^ld_probe_guard C' k bb t /\ SUC h = LENGTH X /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' (EL h X) t = OK u /\
  ^ld_probe_guard C' j bb (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qabbrev_tac `Guard0 = ^ld_probe_guard C' k bb t` >>
  qabbrev_tac `Guard1 = ^ld_probe_guard C' j bb
    (u with vs_inst_idx := SUC t.vs_inst_idx)` >>
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >> fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ir_supply_covers_fn f.lf_supply fn` by
    (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_sync_supply_covered >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY inst_wf (fn_insts fn)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >>
     simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_def,
          MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[fn_insts_blocks_MEM]) >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
    (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`p`, `f.lf_supply`] >> simp[]) >>
  `t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb` by
    (irule ld_prefix_control >> goal_assum (drule_at Any) >>
     fs[EVERY_MEM]) >>
  `t0.vs_current_bb = s.vs_current_bb` by metis_tac[ld_sync_control] >>
  `t0.vs_inst_idx = p` by
    (irule lowerDloadExpansionEndpointTheory.ld_sync_envelope_position >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `t.vs_inst_idx = p+h /\ h < LENGTH X` by
    metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_bound,
              lowerDloadSafetyKernelTheory.ld_prefix_position] >>
  Cases_on `lower_dload_function_supply f.lf_supply fn` >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
  `q = fn'` by (qpat_x_assum `fn' = ld_image f` mp_tac >>
    qpat_x_assum `lower_dload_function_supply _ _ = _` mp_tac >>
    gvs[ld_image_def]) >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[] >>
  `lookup_block t.vs_current_bb q.fn_blocks = SOME bb` by metis_tac[] >>
  `~in_revert_forward fn s` by
    (`^ld_probe_guard C' k bb t` by fs[Abbr `Guard0`] >>
     drule_all ld_guarded_source_non_revert >> simp[]) >>
  `EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
     j IN P f.lf_fn.fn_name) (f::fs)` by simp[] >>
  drule_all (SRULE [EVERY_DEF, LENGTH] ld_full_endpoint) >> strip_tac >>
  `^ld_probe_stable lo P Sigma names fs f0 A0 Ar (g::fs)` by
    (irule ld_stable_head_extend >> conj_tac >- simp[] >>
     qexistsl_tac [`A`, `f`] >> simp[] >> metis_tac[]) >>
  `ld_return_cont C fn cs g.lf_src` by
    (fs[] >> irule ld_return_cont_next >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    (drule_all venomInstPropsTheory.step_preserves_control_flow >> simp[]) >>
  `~is_terminator (EL h X).inst_opcode` by fs[EVERY_EL] >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `step_inst fuel C' _ t = OK u`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_control_flow) >> simp[]) >>
  `?ti. get_instruction bb (SUC t.vs_inst_idx) = SOME ti` by
    (mp_tac (Q.INST [`C` |-> `C'`, `k` |-> `j`,
         `t` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`]
       ld_successful_body_fetch) >> fs[Abbr `Guard1`, ADD1] >> metis_tac[]) >>
  `fn' = FST (lower_dload_function_supply f.lf_supply fn)` by metis_tac[pairTheory.FST] >>
  `active_inst fn' ti (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (simp[NoAsms, active_inst_def] >> qexists_tac `bb` >>
     fs[get_instruction_def, ADD1] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[] >>
  `?next Y. active_inst fn next (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
     ld_envelope f.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
       (SUC s.vs_inst_idx) Y (p+LENGTH X) /\ 0 < LENGTH Y /\ ti = EL 0 Y` by
    (irule (Q.INST [`q` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`]
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_head) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`fn'`,`s`,`t`,`u`] >> simp[NoAsms] >> metis_tac[]) >>
  `active_inst fn next g.lf_src` by fs[] >>
  `ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
     (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt Ar (g::fs) N` by
    metis_tac[] >>
  simp[NoAsms, Abbr `Goal`] >>
  qexistsl_tac [`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,
    `next`,`g.lf_src`,`g.lf_tgt`,`Ar`,`g::fs`,`N`,`Y`,`p+LENGTH X`,`0`] >>
  simp[NoAsms, lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
  fs[ADD1] >> metis_tac[ld_image_def]
QED

val _ = if null (hyp ld_return_point_endpoint_next) then ()
        else raise Fail "endpoint return point has hypotheses";

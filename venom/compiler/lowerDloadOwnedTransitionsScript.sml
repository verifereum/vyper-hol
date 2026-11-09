(* Unguarded evolution of correlated owned target prefixes. *)
Theory lowerDloadOwnedTransitions
Ancestors
  lowerDloadOwnedTransitionBoundary lowerDloadReturnInterior
  lowerDloadSafetyKernel lowerDloadSafetyRelation lowerDloadSafetyAmbient
  lowerDloadEnvelopeControl lowerDloadSafetyLocations
  venomExecSemantics venomInstProps o1PassContract contextCodegenRel list
  lowerDloadFullEndpoint lowerDloadReturnStable lowerDloadReturnAlignment
  lowerDloadSafetyControlCoverage lowerDloadReturnOrdinary
  venomWf venomInst venomState ptrDiscipline arithmetic o1ContractLowerDload
Libs lowerDloadOwnedTransitionPackageLib lowerDloadReturnPackageLib

Theorem ld_owned_interior_next:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  fn' = ld_image f /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ t0.vs_inst_idx = p /\
  SUC h < LENGTH X /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst 0 C' (EL h X) t = OK u ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' (EL (SUC h) X)
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
    (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`p`, `f.lf_supply`] >> simp[]) >>
  `t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb` by
    (irule ld_prefix_control >> goal_assum (drule_at Any) >> fs[EVERY_MEM]) >>
  `t0.vs_current_bb = s.vs_current_bb` by metis_tac[ld_sync_control] >>
  `t.vs_inst_idx = p+h` by metis_tac[ld_prefix_position] >>
  `~is_terminator (EL h X).inst_opcode` by
    (fs[EVERY_EL] >> `h < LENGTH X` by decide_tac >> metis_tac[]) >>
  `u.vs_current_bb = t.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[]) >>
  `fn' = FST (lower_dload_function_supply f.lf_supply fn)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `active_inst fn' (EL (SUC h) X) (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (asm_rewrite_tac[] >> irule ld_envelope_target_at >>
     simp[] >> qexistsl_tac [`s.vs_inst_idx`,`p`,`s`] >> simp[]) >>
  `ld_prefix C' fn' X p (SUC h) t0 (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ld_prefix_next >> metis_tac[]) >>
  simp[NoAsms, Abbr `Goal`] >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`f::fs`,`N`,`X`,`p`,`SUC h`] >>
  fs[] >> metis_tac[]
QED

Theorem ld_owned_endpoint_next:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  fn' = ld_image f /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ SUC h = LENGTH X /\
  ~in_revert_forward fn s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' (EL h X) t = OK u /\
  active_inst fn' ti (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' ti
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >> fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ir_supply_covers_fn f.lf_supply fn` by
    (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_sync_supply_covered >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[ld_sync_def] >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
    (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`p`, `f.lf_supply`] >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (`t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb` by
       (irule ld_prefix_control >> goal_assum (drule_at Any) >> fs[EVERY_MEM]) >>
     metis_tac[ld_sync_control]) >>
  `~is_terminator (EL h X).inst_opcode` by
    (fs[EVERY_EL] >> `h < LENGTH X` by decide_tac >> metis_tac[]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[]) >>
  drule_all (SRULE [EVERY_DEF, LENGTH] ld_full_endpoint) >> strip_tac >>
  `^ld_probe_stable lo P Sigma names fs f A Ar (g::fs)` by
    (irule ld_stable_head_extend >> conj_tac >- simp[] >>
     qexistsl_tac [`A`, `f`] >> simp[] >> metis_tac[]) >>
  suspend "align"
QED

Resume ld_owned_endpoint_next[align]:
  `ss.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[]) >>
  `fn' = FST (lower_dload_function_supply f.lf_supply fn)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  drule_all (SRULE [] (Q.INST
    [`q` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`]
    ld_envelope_successor_head)) >> strip_tac >>
  `active_inst fn next g.lf_src` by fs[] >>
  `ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
     (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt Ar (g::fs) N` by metis_tac[] >>
  simp[NoAsms, Abbr `Goal`] >>
  qexistsl_tac [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,
    `fn`,`next`,`g.lf_src`,`g.lf_tgt`,`Ar`,`g::fs`,`N`,`Y`,`p+LENGTH X`,`0`] >>
  simp[NoAsms, ld_prefix_zero] >> fs[ADD1] >> metis_tac[ld_image_def]
QED
Finalise ld_owned_endpoint_next

Theorem ld_owned_control_entry:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  fn' = ld_image f /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C' inst t = OK q /\ ~q.vs_halted /\
  enters_block fn' q t1 /\ active_inst fn' ti t1 ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t1
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  `taint_ok fn tn inst s` by
    (drule ld_sync_source >> strip_tac >> fs[ptr_discipline_def] >> metis_tac[]) >>
  `enters_block (ld_image f) q t1 /\ active_inst (ld_image f) ti t1` by metis_tac[] >>
  `o1_ctx_shape C /\ ld_global lo A (f::fs) /\
   EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
   EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
     j IN P f.lf_fn.fn_name) (f::fs) /\
   (!j k. j < k /\ k < LENGTH (f::fs) ==>
     list_precedes (EL j (f::fs)).lf_fn.fn_name
                   (EL k (f::fs)).lf_fn.fn_name names)` by fs[] >>
  drule_all ld_sync_control_entry >> strip_tac >>
  `^ld_probe_stable lo P Sigma names fs f A A (g::fs)` by
    (irule ld_stable_head_replace >> conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `f` >> asm_rewrite_tac[] >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  simp[NoAsms, Abbr `Goal`] >>
  qexistsl_tac [`stk`,`PG`,`ld_erase A o_f H'`,
    `entry_taint_vars fn (jump_to lbl s) tn`,`fn`,`ni`,`s1`,`t1`,
    `A`,`g::fs`,`N`,`X`,`t1.vs_inst_idx`,`0`] >>
  qpat_x_assum `MEM inst.inst_opcode [JMP; JNZ; DJMP]` kall_tac >>
  gvs[] >> metis_tac[]
QED

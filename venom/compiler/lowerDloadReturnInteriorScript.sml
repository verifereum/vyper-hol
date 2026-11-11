(* Structural interior transport and nonterminal return reconstruction. *)
Theory lowerDloadReturnInterior
Ancestors
  lowerDloadReturnNonterminal lowerDloadReturnAlignment lowerDloadSafetyKernel
  lowerDloadSafetyLocations lowerDloadConfiguredOrigins lowerDloadSafetyRelation
  lowerDloadEnvelopeControl venomExecSemantics venomInst venomExecProofs
  list rich_list arithmetic contextCodegenRel
Libs
  lowerDloadReturnPackageLib

Theorem ld_envelope_target_at:
  ld_envelope supply fn s j X p /\ h < LENGTH X /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = p+h ==>
  active_inst (FST (lower_dload_function_supply supply fn)) (EL h X) t
Proof
  simp[ld_envelope_def] >> strip_tac >>
  Cases_on `lower_dload_function_supply supply fn` >>
  drule lower_dload_function_supply_block_at >>
  disch_then (qspec_then `bi` mp_tac) >> simp[] >> strip_tac >>
  drule_all lower_dload_insts_supply_at >> strip_tac >> gvs[] >>
  simp[active_inst_def] >>
  qmatch_asmsub_abbrev_tac `q.fn_blocks = bs ++ [b] ++ rest` >>
  qexists_tac `b` >>
  simp[Abbr `b`, EL_APPEND, get_instruction_def]
QED

Theorem ld_return_point_interior_next:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  fn' = ld_image f /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ t0.vs_inst_idx = p /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\ SUC h < LENGTH X /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst 0 C' (EL h X) t = OK u ==>
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[lowerDloadSafetyAmbientTheory.o1_fn_shape_components]) >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
    (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`p`, `f.lf_supply`] >> simp[]) >>
  `t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb` by
    (irule ld_prefix_control >> goal_assum (drule_at Any) >> fs[EVERY_MEM]) >>
  `t0.vs_current_bb = s.vs_current_bb` by metis_tac[ld_sync_control] >>
  `t.vs_inst_idx = p+h` by metis_tac[ld_prefix_position] >>
  `~is_terminator (EL h X).inst_opcode /\ (EL h X).inst_opcode <> INVOKE` by
    (fs[EVERY_EL] >> `h < LENGTH X` by decide_tac >> metis_tac[]) >>
  `u.vs_current_bb = t.vs_current_bb` by
    (drule_all venomInstPropsTheory.step_preserves_control_flow >> simp[]) >>
  `fn' = FST (lower_dload_function_supply f.lf_supply fn)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `active_inst fn' (EL (SUC h) X) (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (asm_rewrite_tac[] >> irule ld_envelope_target_at >>
     simp[] >> qexistsl_tac [`s.vs_inst_idx`,`p`,`s`] >> simp[]) >>
  `ld_prefix C' fn' X p (SUC h) t0 (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ld_prefix_next >> metis_tac[]) >>
  simp[NoAsms, Abbr `Goal`] >>
  qexistsl_tac [`PG`,`G`,`tn`,`inst`,`s`,`t0`,`A`,`f::fs`,`N`,`X`,`p`,`SUC h`] >>
  fs[] >> metis_tac[]
QED

Theorem ld_envelope_source_nonterminal:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ ld_envelope supply fn s s.vs_inst_idx X p /\
  h < LENGTH X /\ ~is_terminator (EL h X).inst_opcode /\
  (EL h X).inst_opcode <> INVOKE ==>
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DLOAD`
  >- simp[is_terminator_def] >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- simp[is_terminator_def] >>
  drule_all ld_envelope_ordinary >> strip_tac >> gvs[] >>
  `h = 0` by fs[] >> gvs[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "interior transport has hypotheses")
  [ld_envelope_target_at, ld_return_point_interior_next, ld_envelope_source_nonterminal];

Theorem ld_return_point_nonterminal_next:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t /\
  get_instruction bb t.vs_inst_idx = SOME ti /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst_base ti t = OK u /\
  ^ld_probe_guard C' j bb (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qabbrev_tac `Guard1 = ^ld_probe_guard C' j bb (u with vs_inst_idx := SUC t.vs_inst_idx)` >>
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  drule_all ld_point_alignment >> strip_tac >>
  qpat_x_assum `^ld_probe_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `ti = EL h X` by metis_tac[optionTheory.SOME_11] >>
  `o1_ctx_shape C` by fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[lowerDloadSafetyAmbientTheory.o1_fn_shape_components]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (irule ld_envelope_source_nonterminal >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `step_inst 0 C' ti t = OK u` by simp[step_inst_non_invoke] >>
  `step_inst 0 C' (EL h X) t = OK u` by metis_tac[] >>
  Cases_on `frames` >- fs[] >> rename1 `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ (f::fs') _` >>
  `fs' = fs` by fs[] >> qpat_x_assum `fs' = fs` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [HD, TL]) >>
  Cases_on `SUC h < LENGTH X`
  >- (drule_all ld_return_point_interior_next >> simp[NoAsms, Abbr `Goal`]) >>
  `SUC h = LENGTH X` by decide_tac >>
  qpat_x_assum `ti = EL h X` SUBST_ALL_TAC >>
  `^ld_probe_guard C' j bb t` by
    (`step_inst j C' (EL h X) t = OK u` by simp[step_inst_non_invoke] >>
     `run_block_non_phis j C' bb t =
      run_block_non_phis j C' bb (u with vs_inst_idx := SUC t.vs_inst_idx)` by
       (CONV_TAC (LHS_CONV (REWR_CONV run_block_non_phis_def)) >> simp[]) >>
     fs[Abbr `Guard1`] >> metis_tac[]) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[ld_sync_def] >>
  `^ld_probe_guard C' j bb (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[markerTheory.Abbrev_def] >>
  drule_all ld_return_point_endpoint_next >> simp[NoAsms, Abbr `Goal`]
QED

Theorem ld_return_nonterminal_S:
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst_base ti t = z /\
  ((?u. z = OK u) \/ (?rt u. z = IntRet rt u)) ==>
  ^ld_probe_S ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
    k ctx ti t z
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  qabbrev_tac `Point = ^ld_probe_point` >>
  qabbrev_tac `Terminal = ^ld_probe_terminal` >>
  strip_tac
  >- (simp[NoAsms] >> rpt gen_tac >>
      strip_tac >> simp[] >> gen_tac >> disch_tac >>
      `step_inst_base ti t = OK u` by metis_tac[] >>
      `^ld_probe_guard ctx j bb (u with vs_inst_idx := SUC t.vs_inst_idx)` by
        (simp[NoAsms] >> metis_tac[]) >>
      qunabbrev_tac `Ambient` >> qunabbrev_tac `Point` >>
      drule_all ld_return_point_nonterminal_next >> simp[NoAsms]) >>
  qpat_x_assum `z = IntRet rt u` SUBST_ALL_TAC >>
  drule opcodeClassTheory.step_inst_base_intret_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "nonterminal production has hypotheses")
  [ld_return_point_nonterminal_next, ld_return_nonterminal_S];

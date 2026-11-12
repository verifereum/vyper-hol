(* Branch reconstruction retaining the saved return package witnesses. *)
Theory lowerDloadReturnBranch
Ancestors
  lowerDloadReturnControl lowerDloadReturnAlignment lowerDloadReturnOrdinary
  lowerDloadSafetyControlCoverage lowerDloadEnvelopeControl lowerDloadSafetyPhiEffects
  lowerDloadSafetyAmbient lowerDloadSafetyKernel lowerDloadSafetyLocations
  ptrDiscipline venomExecProofs
  venomExecSemantics venomState venomInst list contextCodegenRel
Libs
  lowerDloadReturnPackageLib

Theorem ld_return_point_branch_entry:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t /\
  get_instruction bb t.vs_inst_idx = SOME ti /\
  MEM ti.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst_base ti t = OK q /\ ~q.vs_halted ==>
  ^ld_probe_entry C' fn'
    (^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names) q
Proof
  strip_tac >>
  drule_all ld_point_alignment >> strip_tac >>
  qpat_x_assum `^ld_probe_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `ti = EL h X` by metis_tac[optionTheory.SOME_11] >>
  `o1_ctx_shape C` by fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
     >- (`~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
           fs[is_terminator_def] >>
         drule_all ld_envelope_nonterminal >>
         simp[EVERY_EL] >> disch_then (qspec_then `h` mp_tac) >>
         fs[is_terminator_def]) >> fs[]) >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> simp[]) >>
  `h = 0` by fs[] >>
  `ti = inst /\ t0 = t` by fs[ld_prefix_zero] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `inst = EL h X` kall_tac >>
  Cases_on `frames` >- fs[] >> rename1 `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ (f::fs') _` >>
  `fs' = fs` by fs[] >> qpat_x_assum `fs' = fs` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [HD, TL]) >>
  `inst.inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM inst.inst_opcode [JMP; JNZ; DJMP]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[]) >>
  `step_inst 0 C' inst t = OK q` by
    (drule step_inst_non_invoke >> disch_then (qspecl_then [`0`,`C'`,`t`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `taint_ok fn tn inst s` by
    (drule ld_sync_source >> strip_tac >> fs[ptr_discipline_def] >> metis_tac[]) >>
  qabbrev_tac `Point = ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names` >>
  qabbrev_tac `Guard = ^ld_probe_guard` >>
  simp[NoAsms] >> rpt gen_tac >> strip_tac >>
  rename1 `Guard C' k nb (tp with vs_inst_idx := _)` >>
  qabbrev_tac `tentry = tp with vs_inst_idx := phi_prefix_length nb.bb_instructions` >>
  `^ld_probe_guard C' k nb tentry` by fs[Abbr `Guard`] >>
  `?tentryi. get_instruction nb tentry.vs_inst_idx = SOME tentryi` by
    (drule ld_successful_body_fetch >> simp[]) >>
  `enters_block (ld_image f) q tentry` by
    (simp[enters_block_def, Abbr `tentry`] >> metis_tac[]) >>
  `active_inst (ld_image f) tentryi tentry` by
    (qpat_x_assum `get_instruction nb _ = SOME tentryi` mp_tac >>
     qpat_x_assum `eval_phis q _ = OK tp` mp_tac >>
     qpat_x_assum `lookup_block q.vs_current_bb _ = SOME nb` mp_tac >>
     qpat_x_assum `fn' = ld_image f` mp_tac >>
     qpat_x_assum `Abbrev (tentry = _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
     gvs[] >> simp[active_inst_def] >> qexists_tac `nb` >>
     fs[get_instruction_def] >>
     drule ld_phis_only_vars >> disch_then SUBST1_TAC >> simp[] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_global lo A (f::fs) /\
   EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
   EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) (f::fs) /\
   (!j k. j < k /\ k < LENGTH (f::fs) ==>
      list_precedes (EL j (f::fs)).lf_fn.fn_name
        (EL k (f::fs)).lf_fn.fn_name names)` by fs[] >>
  drule_all ld_sync_control_entry >> strip_tac >>
  `^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)` by
    (irule ld_stable_head_replace >> conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `f` >> asm_rewrite_tac[] >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `is_terminator inst.inst_opcode` by
    (qpat_x_assum `MEM inst.inst_opcode [JMP; JNZ; DJMP]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  `~(jump_to lbl s).vs_halted` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ s t _ (f::fs) _`
       (mp_then Any mp_tac ld_sync_memory) >> strip_tac >>
     qpat_x_assum `ld_nonghost tn s t` mp_tac >>
     qpat_x_assum `~q.vs_halted` mp_tac >>
     qpat_x_assum `q = jump_to lbl t` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[lowerDloadSafetyKernelTheory.ld_nonghost_def, jump_to_def]) >>
  `ld_return_cont C fn cs s1` by (drule_all ld_return_cont_block >> simp[]) >>
  `lookup_block tentry.vs_current_bb fn'.fn_blocks = SOME nb` by
    (simp[NoAsms, Abbr `tentry`] >>
     drule ld_phis_only_vars >> disch_then SUBST1_TAC >>
     simp[NoAsms] >> asm_rewrite_tac[]) >>
  qunabbrev_tac `Point` >> simp[NoAsms] >>
  qexistsl_tac [`PG`,`ld_erase A o_f H'`,`entry_taint_vars fn (jump_to lbl s) tn`,
    `ni`,`s1`,`tentry`,`A`,`g::fs`,`N`,`X'`,`tentry.vs_inst_idx`,`0`] >>
  qpat_x_assum `^ld_probe_stable _ _ _ _ _ _ _ _ (g::fs)` mp_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ s1 tentry _ _ _` mp_tac >>
  qpat_x_assum `ld_envelope g.lf_supply _ _ _ _ _` mp_tac >>
  qpat_x_assum `ld_prefix _ _ X' _ _ _ _` mp_tac >>
  qpat_x_assum `fn' = ld_image f` mp_tac >>
  qpat_x_assum `ld_image f = ld_image g` mp_tac >>
  qpat_x_assum `lookup_block tentry.vs_current_bb _ = SOME nb` mp_tac >>
  qpat_x_assum `ld_return_cont C fn cs s1` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[NoAsms] >> rpt strip_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

val _ = if null (hyp ld_return_point_branch_entry) then ()
        else raise Fail "ld_return_point_branch_entry has hypotheses";

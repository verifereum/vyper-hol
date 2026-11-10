(* Reconstruction at terminating target instructions. *)
Theory lowerDloadReturnTerminating
Ancestors
  lowerDloadReturnEffects lowerDloadReturnTerminal lowerDloadReturnBranch
  lowerDloadOracleCallAssembly
  lowerDloadReturnAlignment lowerDloadEnvelopeControl lowerDloadSafetyAmbient
  lowerDloadSafetyLocations lowerDloadSafetyRelation lowerDloadSafetyKernel opcodeClass ptrDiscipline
  o1PassContract venomExecSemantics venomInst list
Libs
  lowerDloadReturnPackageLib

Theorem ld_return_point_terminal:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t /\
  get_instruction bb t.vs_inst_idx = SOME ti /\
  step_inst_base ti t = IntRet rt u ==>
  ^ld_probe_terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u
Proof
  strip_tac >>
  drule_all ld_point_alignment >> strip_tac >>
  qpat_x_assum `^ld_probe_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `ti = EL h X` by metis_tac[optionTheory.SOME_11] >>
  `o1_ctx_shape C` by fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `is_terminator ti.inst_opcode` by
    (drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]) >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
     >- (`~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
           fs[is_terminator_def] >>
         drule_all ld_envelope_nonterminal >>
         simp[EVERY_EL] >> disch_then (qspec_then `h` mp_tac) >> gvs[]) >> fs[]) >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> simp[]) >>
  `h = 0` by fs[] >>
  `ti = inst /\ t0 = t` by fs[ld_prefix_zero] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `inst = EL h X` kall_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_sync_source >> strip_tac >>
     drule_all ld_frame_reachable_certificate >> simp[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `no_raw_fmp_ops fn` by fs[fmp_free_ctx_def, EVERY_MEM] >>
  `inst.inst_opcode = RET` by
    (`~is_raw_fmp_opcode inst.inst_opcode` by
       fs[no_raw_fmp_ops_def, EVERY_MEM] >>
     drule step_inst_base_intret_opcodes >> strip_tac >>
     gvs[is_raw_fmp_opcode_def]) >>
  `ptr_discipline lo C vs0` by fs[] >>
  drule_all ld_sync_ret_effect >> strip_tac >>
  irule ld_return_terminal_package >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

val _ = if null (hyp ld_return_point_terminal) then ()
        else raise Fail "ld_return_point_terminal has hypotheses";

Theorem ld_return_terminating_S:
  is_terminator ti.inst_opcode /\ step_inst_base ti t = z /\
  ((?u. z = OK u) \/ (?rt u. z = IntRet rt u)) ==>
  ^ld_probe_S ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal k ctx ti t z
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  qabbrev_tac `Point = ^ld_probe_point` >>
  qabbrev_tac `Terminal = ^ld_probe_terminal` >>
  strip_tac >> simp[NoAsms] >> rpt gen_tac >> strip_tac >>
  simp[]
  >- (strip_tac >>
      `MEM ti.inst_opcode [JMP; JNZ; DJMP]` by
        (`step_inst_base ti t = OK u` by metis_tac[] >>
         qpat_x_assum `step_inst_base ti t = OK u` mp_tac >>
         qpat_x_assum `is_terminator ti.inst_opcode` mp_tac >>
         rpt (pop_assum kall_tac) >>
         Cases_on `ti.inst_opcode` >> simp[is_terminator_def] >>
         once_rewrite_tac[step_inst_base_def] >> pure_asm_rewrite_tac[] >> simp[] >>
         simp[AllCaseEqs()] >> rpt strip_tac >> pairarg_tac >> gvs[]) >>
      `step_inst_base ti t = OK u` by metis_tac[] >>
      qpat_x_assum `Abbrev (Terminal = _)` kall_tac >>
      qunabbrev_tac `Ambient` >> qunabbrev_tac `Point` >>
      drule_all ld_return_point_branch_entry >> simp[]) >>
  `step_inst_base ti t = IntRet rt u` by metis_tac[] >>
  qunabbrev_tac `Ambient` >> qunabbrev_tac `Point` >> qunabbrev_tac `Terminal` >>
  drule_all ld_return_point_terminal >> simp[]
QED

val _ = if null (hyp ld_return_terminating_S) then ()
        else raise Fail "ld_return_terminating_S has hypotheses";

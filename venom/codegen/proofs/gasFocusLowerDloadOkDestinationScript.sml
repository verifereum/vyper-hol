(* Recover the bounded point selected by the actual successful terminator. *)
Theory gasFocusLowerDloadOkDestination
Ancestors
  gasFocusLowerDloadJumpContinuation gasFocusLowerDloadSelectedBranchContinuation
  lowerDloadNormalJump lowerDloadEnvelopeControl lowerDloadSafetyAmbient
  lowerDloadSafetyLocations
  lowerDloadSafetyRelation lowerDloadSafetyKernel o1ContractLowerDload
  o1PassContract o1SafeUpto opcodeClass venomExecSemantics venomInst list
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_ok_destination_point:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
  gn = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' gn X p h t0 t /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  s.vs_gas_readings = t0.vs_gas_readings /\
  t0.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames /\
  get_instruction bb t.vs_inst_idx = SOME ti /\
  is_terminator ti.inst_opcode /\ step_inst k C' ti t = OK q /\ ~q.vs_halted /\
  lookup_block q.vs_current_bb gn.fn_blocks = SOME bb' /\
  eval_phis q bb'.bb_instructions = OK tp /\
  (run_block_non_phis m C' bb' (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = z /\
     ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v))) ==>
  ?PG1 G1 tn1 i s1 b1 A1 frames1 N1 Y p1 h1 j.
    ld_sync lo P C vs stk PG1 G1 tn1 fn i s1 b1 A1 frames1 N1 /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A1 frames1 /\
    gn = ld_image (HD frames1) /\
    ld_envelope (HD frames1).lf_supply fn s1 s1.vs_inst_idx Y p1 /\
    b1.vs_inst_idx = p1 /\ ld_prefix C' gn Y p1 h1 b1 (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    lookup_block (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_current_bb gn.fn_blocks = SOME bb' /\
    get_instruction bb' (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_inst_idx = SOME j /\ h1 < LENGTH Y /\ j = EL h1 Y /\
    ld_return_cont C fn cs s1 /\
    s1.vs_gas_readings = b1.vs_gas_readings /\ b1.vs_gas_readings = (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
               LENGTH s1.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames1
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `frames <> [] /\ (HD frames).lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (qpat_assum `gn = ld_image _` SUBST1_TAC >>
     pure_rewrite_tac[ld_image_def] >>
     qpat_assum `(HD frames).lf_fn = fn` SUBST1_TAC >>
     Cases_on `lower_dload_function_supply (HD frames).lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `active_inst fn inst s` by (drule ld_sync_source >> simp[]) >>
  `active_inst gn (EL h X) t` by metis_tac[ld_prefix_active] >>
  `ti = EL h X` by
    (drule_all ld_active_lookup >> simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
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
  drule_all ld_successful_terminator_branch >> strip_tac >>
  `?f tail. frames = f::tail` by (Cases_on `frames` >> fs[]) >>
  qpat_x_assum `frames = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [HD, TL, NOT_CONS_NIL]) >>
  qpat_x_assum `gn = ld_image _` SUBST_ALL_TAC >>
  let
    fun destination th =
      drule_all (REWRITE_RULE [HD, TL, NOT_CONS_NIL] (BETA_RULE th)) >>
      strip_tac >>
      qpat_x_assum `g = _` kall_tac >>
      qmatch_goalsub_abbrev_tac `lookup_block t1.vs_current_bb _ = SOME bb'` >>
      qexistsl_tac [`PG`,`G'`,`entry_taint_vars fn (jump_to lbl s) tn`,`ni`,
                    `s1`,`t1`,`A`,`g::tail`,`N`,`Y`,`t1.vs_inst_idx`,`0`,`HD Y`] >>
      unabbrev_all_tac >> asm_rewrite_tac[HD, TL, NOT_CONS_NIL, EL]
  in
    Cases_on `inst.inst_opcode = JMP`
    >- destination ld_focus_successful_jump_entry >>
    `MEM inst.inst_opcode [JNZ; DJMP]` by fs[] >>
    destination ld_focus_successful_selected_branch_entry
  end
QED

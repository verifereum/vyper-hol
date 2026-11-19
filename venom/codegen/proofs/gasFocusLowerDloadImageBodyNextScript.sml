(* Follow the actual evaluator suffix through a changed LowerDload image. *)
Theory gasFocusLowerDloadImageBodyNext
Ancestors
  gasFocusLowerDloadWriteCopyDispatch gasFocusLowerDloadScratchBody
  gasFocusLowerDloadCutGuards lowerDloadExpansionEndpoint lowerDloadEnvelopeControl
  lowerDloadReturnInterior lowerDloadReturnOrdinary lowerDloadPublicTrace
  lowerDloadSafetyLocations lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadSafetyAmbient lowerDloadForwardingCoverage lowerDloadReturnAlignment
  lowerDloadDefs o1ContractLowerDload o1PassContract o1SafeUpto gasCount
  venomInstProps venomExecSemantics venomInst opcodeClass list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_image_body_next:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ o1_safe_upto D lo n C vs /\
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
  ir_supply_covers_fn (HD frames).lf_supply fn /\
  X <> [inst] /\ ti.inst_opcode <> INVOKE /\ ~is_terminator ti.inst_opcode /\
  step_inst fuel C' ti t = OK u /\
  (run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
     ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v))) ==>
  ?PG1 G1 tn1 i s1 b1 A1 frames1 N1 Y p1 h1 j.
    ld_sync lo P C vs stk PG1 G1 tn1 fn i s1 b1 A1 frames1 N1 /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A1 frames1 /\
    gn = ld_image (HD frames1) /\
    ld_envelope (HD frames1).lf_supply fn s1 s1.vs_inst_idx Y p1 /\
    b1.vs_inst_idx = p1 /\ ld_prefix C' gn Y p1 h1 b1 (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    lookup_block (u with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb gn.fn_blocks = SOME bb /\
    get_instruction bb (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME j /\ h1 < LENGTH Y /\ j = EL h1 Y /\
    ld_return_cont C fn cs s1 /\
    s1.vs_gas_readings = b1.vs_gas_readings /\ b1.vs_gas_readings = (u with vs_inst_idx := SUC t.vs_inst_idx).vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
               LENGTH s1.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames1
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `MEM ti.inst_opcode [MSTORE;MSTORE8;MCOPY;CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
  >- (drule_all (BETA_RULE (REWRITE_RULE [LET_THM] ld_focus_write_copy_successor_point)) >> simp[]) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule ld_sync_source >> strip_tac >>
  `(HD frames).lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `gn = FST (lower_dload_function_supply (HD frames).lf_supply fn)` by
    simp[ld_image_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (qpat_assum `gn = FST _` SUBST1_TAC >>
     Cases_on `lower_dload_function_supply (HD frames).lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `active_inst gn (EL h X) t` by metis_tac[ld_prefix_active] >>
  `ti = EL h X` by
    (drule_all (Q.INST [`inst` |-> `EL h X`] ld_active_lookup) >>
     simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `t0.vs_inst_idx = p` by
    (Cases_on `frames` >> fs[] >> drule_all ld_sync_envelope_position >> simp[]) >>
  `u.vs_current_bb = t.vs_current_bb` by (drule_all step_preserves_control_flow >> simp[]) >>
  `lookup_block q.vs_current_bb gn.fn_blocks = SOME bb` by (simp[Abbr `q`] >> (metis_tac[Abbr `q`])) >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  Cases_on `SUC h < LENGTH X` >- suspend "interior" >>
  `SUC h = LENGTH X` by decide_tac >> suspend "last"
QED

Resume ld_focus_image_body_next[interior]:
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (`inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES` by
       metis_tac[ld_envelope_ordinary] >> fs[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) X` by
    (drule_all ld_envelope_nonterminal >> simp[EVERY_MEM] >> metis_tac[]) >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + SUC h` by
    (drule_all ld_prefix_control >> strip_tac >>
     drule ld_sync_control >> strip_tac >>
     `t.vs_inst_idx = p+h` by metis_tac[ld_prefix_position] >> simp[Abbr `q`]) >>
  `active_inst gn (EL (SUC h) X) q` by
    (qpat_assum `gn = FST _` SUBST1_TAC >> irule ld_envelope_target_at >> simp[] >>
     qexistsl_tac [`s.vs_inst_idx`,`s`] >> simp[]) >>
  `j = EL (SUC h) X` by
    (drule_all (Q.INST [`inst` |-> `EL (SUC h) X`] ld_active_lookup) >>
     simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `step_inst 0 C' (EL h X) t = OK u` by metis_tac[step_inst_non_invoke] >>
  `ld_prefix C' gn X p (SUC h) t0 q` by
    (qpat_x_assum `Abbrev (q = _)`
       (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all ld_prefix_next >> simp[]) >>
  `q.vs_gas_readings = t0.vs_gas_readings` by
    (irule ld_expansion_prefix_readings >> metis_tac[]) >>
  qexistsl_tac [`PG`,`G`,`tn`,`inst`,`s`,`t0`,`A`,`frames`,`N`,`X`,`p`,`SUC h`,`j`] >>
  simp[] >> metis_tac[]
QED

Resume ld_focus_image_body_next[last]:
  `?f. frames = f::fs` by (Cases_on `frames` >> gns[]) >>
  qpat_x_assum `frames = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [HD, TL]) >>
  `?ui. X = FST (lower_dload_inst_supply ui inst)` by
    (drule_all ld_active_envelope_origin >> metis_tac[]) >>
  reverse (Cases_on `inst.inst_opcode = DLOAD`)
  >- (`inst.inst_opcode = DLOADBYTES` by metis_tac[ld_envelope_ordinary] >>
      `?dest off len. inst.inst_operands = [dest;off;len]` by
        (namedCases_on `inst.inst_operands` ["", "dest ops"] >- gvs[lower_dload_inst_supply_def] >>
         namedCases_on `ops` ["", "off ops1"] >- gvs[lower_dload_inst_supply_def] >>
         namedCases_on `ops1` ["", "len ops2"] >- gvs[lower_dload_inst_supply_def] >>
         Cases_on `ops2` >- simp[] >> gvs[lower_dload_inst_supply_def]) >>
      drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
      `h = 1` by gns[] >> gvs[EL]) >>
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    (namedCases_on `inst.inst_operands` ["", "off ops"]
     >- gvs[lower_dload_inst_supply_def] >>
     reverse (Cases_on `ops`)
     >- (namedCases_on `inst.inst_outputs` ["", "o os"] >- gvs[lower_dload_inst_supply_def] >>
         Cases_on `os` >> gvs[lower_dload_inst_supply_def]) >>
     namedCases_on `inst.inst_outputs` ["", "out outs"]
     >- gvs[lower_dload_inst_supply_def] >>
     Cases_on `outs` >- simp[] >> gvs[lower_dload_inst_supply_def]) >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs t` by
    (irule ld_step_ok_cut_back >> `gas_cut n vs u` by gns[gas_cut_def, Abbr `q`] >>
     metis_tac[]) >>
  `gas_cut n vs s` by gns[gas_cut_def] >>
  `get_instruction bb (SUC t.vs_inst_idx) = SOME j` by gns[Abbr `q`] >>
  qpat_assum `gn = ld_image f` SUBST_ALL_TAC >>
  `step_inst fuel C' (EL h X) t = OK u` by metis_tac[] >>
  drule_all (REWRITE_RULE [HD, TL, NOT_CONS_NIL]
    (Q.INST [`fs0` |-> `fs`] (BETA_RULE (REWRITE_RULE [LET_THM] ld_focus_scratch_body_next)))) >>
  disch_then (qx_choose_then `ss` (qx_choose_then `g`
    (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)))) >>
  qexistsl_tac [`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,`i`,
                `g.lf_src`,`q`,`A`,`g::fs`,`N`,`Y`,`q.vs_inst_idx`,`0`,`j`] >>
  gns[Abbr `q`, HD, EL] >> metis_tac[ld_prefix_bound]
QED

Finalise ld_focus_image_body_next

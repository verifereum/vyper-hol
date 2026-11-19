(* Resume the actual bounded body at a write or copy in a LowerDload image. *)
Theory gasFocusLowerDloadWriteCopyDispatch
Ancestors contextCodegenRelProps[qualified,ignore_grammar]
  gasFocusLowerDloadMemoryWriteNext gasFocusLowerDloadPublicCopyNext
  gasFocusLowerDloadBytesWrite gasFocusLowerDloadBytesNext
  gasFocusLowerDloadCutGuards lowerDloadExpansionEndpoint
  lowerDloadEnvelopeControl lowerDloadSafetyLocations lowerDloadSafetyRelation
  lowerDloadReturnInterior lowerDloadReturnOrdinary lowerDloadPublicTrace lowerDloadForwardingCoverage
  lowerDloadSafetyAmbient lowerDloadSafetyKernel lowerDloadReturnAlignment
  lowerDloadDefs o1ContractLowerDload o1PassContract o1SafeUpto gasCount venomInstProps
  venomExecSemantics venomInst opcodeClass list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_write_copy_successor_point:
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
  MEM ti.inst_opcode [MSTORE;MSTORE8;MCOPY;CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
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
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `?f. frames = f::fs` by (Cases_on `frames` >> gns[]) >>
  qpat_x_assum `frames = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [HD, TL]) >>
  drule ld_sync_source >> strip_tac >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[HD]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (qpat_assum `gn = ld_image _` SUBST1_TAC >>
     pure_rewrite_tac[ld_image_def] >>
     qpat_assum `f.lf_fn = fn` SUBST1_TAC >>
     Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `active_inst gn (EL h X) t` by metis_tac[ld_prefix_active] >>
  `ti = EL h X` by
    (drule_all ld_active_lookup >> simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `t0.vs_inst_idx = p` by (drule_all ld_sync_envelope_position >> simp[]) >>
  `~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE` by
    (qpat_assum `MEM ti.inst_opcode _` mp_tac >> rewrite_tac[MEM] >>
     strip_tac >> simp[is_terminator_def]) >>
  `u.vs_current_bb = t.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[]) >>
  `lookup_block q.vs_current_bb gn.fn_blocks = SOME bb` by gns[Abbr `q`] >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs t` by
    (irule ld_step_ok_cut_back >> `gas_cut n vs u` by gns[gas_cut_def, Abbr `q`] >>
     metis_tac[]) >>
  `gas_cut n vs s` by gns[gas_cut_def] >>
  Cases_on `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES`
  >- suspend "ordinary" >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode = DLOAD` >- simp[is_terminator_def] >>
     `inst.inst_opcode = DLOADBYTES` by metis_tac[] >> simp[is_terminator_def]) >>
  `X <> [inst]` by
    (strip_tac >> `h = 0` by gns[] >> gvs[EL]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) X` by
    (drule_all ld_envelope_nonterminal >> simp[EVERY_MEM] >> metis_tac[]) >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + SUC h` by
    (drule_all ld_prefix_control >> strip_tac >>
     drule ld_sync_control >> strip_tac >>
     `t.vs_inst_idx = p+h` by metis_tac[ld_prefix_position] >>
     simp[Abbr `q`]) >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by gns[ld_image_def] >>
  Cases_on `inst.inst_opcode = DLOAD` >- suspend "dload" >>
  `inst.inst_opcode = DLOADBYTES` by metis_tac[] >> suspend "bytes"
QED

Resume ld_focus_write_copy_successor_point[ordinary]:
  `X = [inst]` by metis_tac[ld_envelope_ordinary] >>
  `h = 0` by gns[] >>
  qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  `ti = inst` by (qpat_assum `ti = EL 0 [inst]` mp_tac >> simp[]) >>
  `t0 = t` by metis_tac[ld_prefix_zero] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_assum `gn = ld_image f` SUBST_ALL_TAC >>
  `run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z` by
    metis_tac[Abbr `q`] >>
  Q.SUBGOAL_THEN
    `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] \/
     MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
    (DISJ_CASES_THEN2
      (fn th => assume_tac th >> drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
        (REWRITE_RULE [HD, TL, NOT_CONS_NIL]
          (Q.INST [`fs0` |-> `fs`] (BETA_RULE ld_focus_memory_write_body_next))))
      (fn th => assume_tac th >> drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
        (REWRITE_RULE [HD, TL, NOT_CONS_NIL]
          (Q.INST [`fs0` |-> `fs`] (BETA_RULE ld_focus_public_copy_body_next)))))
  >- (qpat_assum `MEM inst.inst_opcode _` mp_tac >> rewrite_tac[MEM] >> metis_tac[]) >>
  rpt (disch_then drule) >>
  disch_then (qx_choose_then `ss` (qx_choose_then `g`
    (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)))) >>
  qexistsl_tac [`PG`, `step_prov PG G inst ss`, `step_taint inst s ss tn`, `i`,
                `ss with vs_inst_idx := SUC s.vs_inst_idx`, `q`, `A`, `g::fs`,
                `N`, `Y`, `SUC t.vs_inst_idx`, `0`, `HD Y`] >>
  gnvs[Abbr `q`, EL] >> rpt strip_tac >>
  qpat_assum `!g. MEM g fs ==> _` (drule_all o cj 2) >> simp[]
QED

Resume ld_focus_write_copy_successor_point[dload]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    (drule_all ld_active_envelope_origin >> strip_tac >>
     qpat_x_assum `X = FST (lower_dload_inst_supply _ _)` mp_tac >>
     simp[lower_dload_inst_supply_def] >>
     namedCases_on `inst.inst_operands` ["", "off ops"] >- simp[] >>
     Cases_on `ops` >- (
       namedCases_on `inst.inst_outputs` ["", "out outs"] >- simp[] >>
       Cases_on `outs` >> simp[]) >>
     namedCases_on `inst.inst_outputs` ["", "out outs"] >- simp[] >>
     Cases_on `outs` >> simp[]) >>
  `LENGTH X = 4 /\ h = 2` by
    (drule_all ld_dload_envelope_temporary >> strip_tac >>
     `h < 4` by gns[] >>
     Q.SUBGOAL_THEN `h = 0 \/ h = 1 \/ h = 2 \/ h = 3` strip_assume_tac
     >- decide_tac >> gvs[EL]) >>
  `SUC h < LENGTH X` by gns[] >>
  `active_inst gn (EL (SUC h) X) q` by
    (qpat_assum `gn = FST _` SUBST1_TAC >> irule ld_envelope_target_at >> simp[] >>
     qexistsl_tac [`s.vs_inst_idx`,`s`] >> simp[]) >>
  `j = EL (SUC h) X` by
    (drule_all ld_active_lookup >> simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `step_inst 0 C' (EL h X) t = OK u` by
    metis_tac[step_inst_non_invoke] >>
  `ld_prefix C' gn X p (SUC h) t0 q` by
    (qpat_x_assum `Abbrev (q = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all ld_prefix_next >> simp[]) >>
  `q.vs_gas_readings = t0.vs_gas_readings` by
    (irule ld_expansion_prefix_readings >> metis_tac[]) >>
  qexistsl_tac [`PG`,`G`,`tn`,`inst`,`s`,`t0`,`A`,`f::fs`,`N`,`X`,`p`,`SUC h`,`j`] >>
  simp[]
  >> (metis_tac[])
QED

Resume ld_focus_write_copy_successor_point[bytes]:
  `?dest off len. inst.inst_operands = [dest;off;len]` by
    (drule_all ld_active_envelope_origin >> strip_tac >>
     qpat_x_assum `X = FST (lower_dload_inst_supply _ _)` mp_tac >>
     simp[lower_dload_inst_supply_def] >>
     namedCases_on `inst.inst_operands` ["", "dest ops"] >- simp[] >>
     namedCases_on `ops` ["", "off ops1"] >- simp[] >>
     namedCases_on `ops1` ["", "len ops2"] >- simp[] >>
     Cases_on `ops2` >> simp[]) >>
  `LENGTH X = 2 /\ h = 1` by
    (drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
     `h < 2` by gns[] >>
     Q.SUBGOAL_THEN `h = 0 \/ h = 1` strip_assume_tac
     >- decide_tac >> gvs[EL]) >>
  `~in_revert_forward fn s` by
    (strip_tac >> drule_all ld_forward_envelope_singleton >> simp[]) >>
  qpat_x_assum `h = 1` SUBST_ALL_TAC >>
  `step_inst fuel C' (EL 1 X) t = OK u` by metis_tac[] >>
  drule_all (Q.INST [`t1` |-> `t`] ld_focus_bytes_classified_write) >>
  disch_then (qx_choose_then `ss` (qx_choose_then `bs` (qx_choose_then `dw`
    (qx_choose_then `dw'` (qx_choose_then `ow` (qx_choose_then `nw`
      (qx_choose_then `zv` (qx_choose_then `v`
        (map_every assume_tac o CONJUNCTS))))))))) >>
  `lo <= vs.vs_alloca_next /\ mem_inv dload_headroom_ok C vs` by
    (qpat_assum `o1_safe_upto _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE
          [o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def]) >>
     simp[]) >>
  drule_all (Q.INST [`t1` |-> `t`]
    (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV) ld_focus_bytes_classified_next)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `active_inst gn j q` by (drule_all contextCodegenRelPropsTheory.lookup_instruction_active >> (simp[contextCodegenRelPropsTheory.lookup_instruction_active])) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `ss = write_memory_with_expansion _ _ _` SUBST1_TAC >>
     simp[venomStateTheory.write_memory_with_expansion_def]) >>
  `q.vs_inst_idx = p + LENGTH X` by
    (qpat_assum `SUC t.vs_inst_idx = p + LENGTH X` (SUBST1_TAC o SYM) >>
     simp[Abbr `q`]) >>
  drule_all ld_envelope_successor_head >>
  disch_then (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)) >>
  qabbrev_tac `ss1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := ss1; lf_tgt := q|>` >>
  `ld_return_cont C fn cs ss1` by
    (simp[Abbr `ss1`] >> drule_all ld_return_cont_next >> simp[]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn i ss1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (qpat_assum `!next. active_inst _ next _ ==> _` (qspec_then `i` mp_tac) >>
     simp[Abbr `g`, Abbr `ss1`, Abbr `q`, NoAsms] >>
     qpat_assum `active_inst fn i _` assume_tac >>
     qpat_assum `ld_global lo A (_::fs)` mp_tac >>
     (metis_tac[Abbr `g`, Abbr `ss1`, Abbr `q`])) >>
  Q.SUBGOAL_THEN `^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)`
    (assume_tac o BETA_RULE)
  >- (BETA_TAC >> MATCH_MP_TAC (BETA_RULE ld_stable_head_replace) >>
      conj_tac
      >- (pure_rewrite_tac[HD, TL, NOT_CONS_NIL] >> asm_rewrite_tac[]) >>
      conj_tac >- simp[Abbr `g`, NoAsms] >>
      conj_tac >- simp[Abbr `g`, NoAsms] >>
      conj_tac >- simp[Abbr `g`, NoAsms] >>
      conj_tac >- simp[Abbr `g`, NoAsms] >>
      first_assum ACCEPT_TAC) >>
  `ss1.vs_inst_idx = SUC s.vs_inst_idx` by simp[Abbr `ss1`] >>
  `ld_prefix C' gn Y (p + LENGTH X) 0 q q` by
    (pure_rewrite_tac[ld_prefix_zero] >> metis_tac[]) >>
  `ss1.vs_gas_readings = s.vs_gas_readings /\ q.vs_gas_readings = s.vs_gas_readings` by
    (simp[Abbr `ss1`, Abbr `q`, NoAsms] >> metis_tac[]) >>
  qexistsl_tac [`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,`i`,
                `ss1`,`q`,`A`,`g::fs`,`N`,`Y`,`p + LENGTH X`,`0`,`j`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[HD] >>
  conj_tac
  >- (qpat_assum `gn = ld_image f` SUBST1_TAC >> simp[Abbr `g`, ld_image_def, NoAsms]) >>
  conj_tac
  >- (qpat_assum `ss1.vs_inst_idx = SUC s.vs_inst_idx` SUBST1_TAC >>
      `g.lf_supply = f.lf_supply` by simp[Abbr `g`, NoAsms] >>
      pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EVERY (\x. x.lf_src.vs_gas_readings = x.lf_tgt.vs_gas_readings /\
                       LENGTH s.vs_gas_readings <= LENGTH x.lf_src.vs_gas_readings) (f::fs)`
    (assume_tac o CONJUNCT2 o BETA_RULE o REWRITE_RULE [EVERY_DEF]) >>
  qpat_assum `ss1.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
  qpat_assum `q.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
  simp[Abbr `g`, NoAsms] >>
  qpat_assum `ss1.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
  qpat_assum `q.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
  rewrite_tac[LESS_EQ_REFL] >> first_assum ACCEPT_TAC
QED

Finalise ld_focus_write_copy_successor_point

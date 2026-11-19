(* Recover the actual callee body point before invoking successful-run induction. *)
Theory gasFocusLowerDloadInvokeFirstBody
Ancestors
  gasFocusLowerDloadCallEntry gasFocusLowerDloadInvokeSetup
  lowerDloadReturnInvokePush lowerDloadReturnAlignment lowerDloadEnvelopeControl
  lowerDloadSafetyLocations lowerDloadSafetyAmbient lowerDloadSafetyRelation
  lowerDloadSafetyKernel o1ContractLowerDload o1PassContract o1SafeUpto
  gasCount gasOracleReplay ptrDiscipline contextCodegenRel
  venomExecProofs venomExecSemantics venomState venomInst list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem invoke_caller_singleton[local]:
  o1_ctx_shape C /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  gn = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' gn X p h t0 t /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME ti /\ ti.inst_opcode = INVOKE ==>
  X = [inst] /\ h = 0 /\ ti = inst /\ t0 = t
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (`(HD frames).lf_fn = fn` by metis_tac[ld_sync_active] >>
     qpat_assum `gn = ld_image _` SUBST1_TAC >>
     pure_rewrite_tac[ld_image_def] >>
     qpat_assum `(HD frames).lf_fn = fn` SUBST1_TAC >>
     Cases_on `lower_dload_function_supply (HD frames).lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `active_inst gn (EL h X) t` by metis_tac[ld_prefix_active] >>
  `ti = EL h X` by
    (drule_all ld_active_lookup >> simp[] >> strip_tac >> gvs[get_instruction_def]) >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES` >>
     gvs[] >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     drule_all ld_envelope_nonterminal >>
     rewrite_tac[EVERY_EL] >> disch_then (qspec_then `h` mp_tac) >> gvs[]) >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> simp[]) >>
  `h = 0` by fs[] >> fs[ld_prefix_zero]
QED

Theorem invoke_return_cut[local]:
  setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel C' calleeT ct = IntRet rt uc /\
  bind_outputs ti.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t uc)) = SOME u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?r v. z = IntRet r v /\ gas_cut n vs v)) ==>
  gas_cut n vs uc /\ gas_cut n vs t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule gas_bind_outputs_readings >> simp[] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `run_block_non_phis fuel C' bb q` >>
  `q.vs_gas_readings = uc.vs_gas_readings` by simp[Abbr `q`] >>
  `gas_cut n vs uc` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  simp[] >>
  drule gas_setup_callee_readings >> disch_tac >>
  qspecl_then [`fuel`,`C'`,`calleeT`,`ct`] mp_tac (CONJUNCT2 (CONJUNCT2 gas_count_suffix)) >>
  simp[gas_count_suffix_def] >> disch_tac >>
  qpat_x_assum `gas_cut n vs uc` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac
QED

Theorem invoke_successful_entry_fetch[local]:
  run_blocks fuel C' calleeT ct = IntRet rt uc ==>
  ?m b cp tp j.
    fuel = SUC m /\
    lookup_block ct.vs_current_bb calleeT.fn_blocks = SOME b /\
    eval_phis ct b.bb_instructions = OK cp /\
    tp = (cp with vs_inst_idx := phi_prefix_length b.bb_instructions) /\
    ^ld_probe_guard C' m b tp /\
    enters_block calleeT ct tp /\ active_inst calleeT j tp /\
    lookup_block tp.vs_current_bb calleeT.fn_blocks = SOME b /\
    get_instruction b tp.vs_inst_idx = SOME j
Proof
  BETA_TAC >> Cases_on `fuel` >- simp[Once run_blocks_def] >>
  once_rewrite_tac[run_blocks_def] >> simp[AllCaseEqs()] >>
  strip_tac >>
  qspecl_then [`ct`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> gvs[] >>
  qmatch_asmsub_abbrev_tac `run_block_non_phis _ _ _ tp` >>
  `^ld_probe_guard C' n bb tp` by (BETA_TAC >> metis_tac[]) >>
  `?j. get_instruction bb tp.vs_inst_idx = SOME j` by metis_tac[ld_successful_body_fetch] >>
  `lookup_block tp.vs_current_bb calleeT.fn_blocks = SOME bb` by
    (drule eval_phis_preserves_current_bb >> simp[Abbr `tp`]) >>
  `active_inst calleeT j tp` by
    (simp[active_inst_def] >> qexists `bb` >> gvs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `enters_block calleeT ct tp` by
    (simp[enters_block_def, Abbr `tp`] >> qexistsl_tac [`bb`,`s'`] >> simp[]) >>
  qexists `j` >> fs[Abbr `tp`]
QED

Theorem ld_focus_invoke_first_body_point:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  callee_first names C.ctx_functions /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A frames /\
  gn = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\ ld_return_cont C fn caller s /\
  s.vs_gas_readings = t0.vs_gas_readings /\ t0.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames /\
  get_instruction bb t.vs_inst_idx = SOME ti /\ ti.inst_opcode = INVOKE /\
  decode_invoke ti = SOME (nm,ops) /\ lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\ setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel C' calleeT ct = IntRet rt uc /\
  bind_outputs ti.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t uc)) = SOME u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?r v. z = IntRet r v /\ gas_cut n vs v)) ==>
  gas_cut n vs uc /\
  ?f fs callee argsS cs saved fc PG1 tn1 i Y m b cp tp j.
    frames = f::fs /\ X = [inst] /\ h = 0 /\ ti = inst /\ t0 = t /\ t.vs_inst_idx = p /\
    lookup_function nm C.ctx_functions = SOME callee /\ callee.fn_name = nm /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    calleeT = FST (lower_dload_function_supply (Sigma nm) callee) /\
    saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
      cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
    fc.lf_serial = N /\ fc.lf_fn = callee /\ fc.lf_supply = Sigma nm /\
    fc.lf_src = cs /\ fc.lf_tgt = ct /\ fc.lf_Q = MAP (op_prov f.lf_H) ops /\
    fuel = SUC m /\ lookup_block ct.vs_current_bb calleeT.fn_blocks = SOME b /\
    eval_phis ct b.bb_instructions = OK cp /\
    tp = (cp with vs_inst_idx := phi_prefix_length b.bb_instructions) /\ tp = ct /\
    ^ld_probe_guard C' m b tp /\
    ld_sync lo P C vs (saved::stk) PG1 FEMPTY tn1 callee i cs ct A (fc::f::fs) (SUC N) /\
    ^ld_probe_stable lo P Sigma names (f::fs) fc A A (fc::f::fs) /\
    calleeT = ld_image fc /\
    ld_envelope fc.lf_supply callee cs cs.vs_inst_idx Y ct.vs_inst_idx /\
    ld_prefix C' calleeT Y ct.vs_inst_idx 0 ct tp /\
    lookup_block tp.vs_current_bb calleeT.fn_blocks = SOME b /\
    get_instruction b tp.vs_inst_idx = SOME j /\ j = EL 0 Y /\
    ld_return_cont C callee cs cs /\
    cs.vs_gas_readings = ct.vs_gas_readings /\ ct.vs_gas_readings = tp.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH cs.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (fc::f::fs)
Proof
  CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all invoke_caller_singleton >> strip_tac >>
  drule_all invoke_return_cut >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  namedCases_on `frames` ["", "f fs"] >- metis_tac[ld_sync_active] >>
  qexistsl_tac [`f`,`fs`] >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `taint_ok fn tn inst s` by
    (drule ld_sync_source >> strip_tac >>
     fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  drule invoke_successful_entry_fetch >> strip_tac >>
  rename1 `eval_phis ct b.bb_instructions = OK cphi` >>
  drule_all ld_focus_invoke_correlated_setup >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) callee.fn_blocks)` by
    (`MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `o1_fn_shape C callee` by (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
     drule o1_fn_shape_components >> simp[]) >>
  `lower_dload_function_supply (Sigma nm) callee =
    (calleeT, SND (lower_dload_function_supply (Sigma nm) callee))` by metis_tac[pairTheory.PAIR] >>
  `ld_return_cont C callee cs cs` by
    (drule_all ld_setup_active_entry >> strip_tac >> irule ld_return_cont_entry >> simp[]) >>
  drule_all (BETA_RULE ld_focus_invoke_active_entry) >> strip_tac >>
  `callee' = callee` by metis_tac[optionTheory.SOME_11] >>
  `cs' = cs` by metis_tac[optionTheory.SOME_11] >>
  `calleeT = ld_image fc` by simp[ld_image_def] >>
  qpat_x_assum `callee' = callee` SUBST_ALL_TAC >>
  qpat_x_assum `cs' = cs` SUBST_ALL_TAC >>
  qpat_x_assum `tp = ct` SUBST_ALL_TAC >>
  qexistsl_tac [`callee`,`argsS`,`cs`,`saved`,`fc`,`PG1`,`tn1`,`i`,`X`,`m`,`b`,`cphi`,`ct`,`j`] >>
  BETA_TAC >> rpt conj_tac >>
  FIRST [REFL_TAC, first_assum (ACCEPT_TAC o BETA_RULE), simp[NoAsms]]
QED

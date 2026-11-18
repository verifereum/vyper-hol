(* Raw INVOKE-next follows the actual completed callee, not a caller suffix. *)
Theory gasFocusLowerDloadRawCompletedInvoke
Ancestors
  gasFocusLowerDloadSuccessfulReturn gasFocusLowerDloadCallEntry
  gasFocusLowerDloadCallReturn gasFocusLowerDloadInvokeSetup
  lowerDloadSafetyRunInduction lowerDloadReturnInvokePush
  lowerDloadExpansionEndpoint lowerDloadEnvelopeControl lowerDloadSafetyLocations
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadReturnAlignment o1SafeUpto o1ContractLowerDload o1PassContract
  gasCount gasOracleReplay venomExecProofs venomExecSemantics venomState
  venomInst contextCodegenRel ptrDiscipline finite_map list rich_list
Libs
  lowerDloadReturnPackageLib

val raw_point = ``\gn ti t.
  ?stk PG G tn fn inst s t0 A f fs N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
    gn = ld_image f /\
    ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
    t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\
    h < LENGTH X /\ ti = EL h X /\
    s.vs_gas_readings = t0.vs_gas_readings /\
    t0.vs_gas_readings = t.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)``;

Theorem completed_callee_first_fetch[local]:
  run_blocks fuel C ctfn ct = IntRet rt uc ==>
  ?bb cp i.
    lookup_block ct.vs_current_bb ctfn.fn_blocks = SOME bb /\
    eval_phis ct bb.bb_instructions = OK cp /\
    enters_block ctfn ct
      (cp with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    active_inst ctfn i
      (cp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  Cases_on `fuel` >- simp[Once run_blocks_def] >>
  once_rewrite_tac[run_blocks_def] >> simp[AllCaseEqs()] >>
  strip_tac >>
  qspecl_then [`ct`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> gvs[] >>
  qmatch_asmsub_abbrev_tac `run_block_non_phis _ _ _ tp` >>
  `^ld_probe_guard C n bb tp` by (BETA_TAC >> metis_tac[]) >>
  `?i. get_instruction bb tp.vs_inst_idx = SOME i` by
    metis_tac[BETA_RULE ld_successful_body_fetch] >>
  qexists `i` >> conj_tac
  >- (simp[enters_block_def, Abbr `tp`] >> qexistsl_tac [`bb`,`s'`] >> simp[]) >>
  simp[active_inst_def] >>> NTH_GOAL (simp[contextCodegenRelTheory.enters_block_def]) 2 >> qexists `bb` >>
  drule eval_phis_preserves_current_bb >> simp[] >>
  gvs[Abbr `tp`, get_instruction_def] >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem ld_focus_raw_completed_invoke:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY pre_fmp_ops C.ctx_functions /\ o1_safe_upto D lo n C vs /\
  callee_first names C.ctx_functions /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  (!g. MEM g C.ctx_functions ==> ir_supply_covers_fn (Sigma g.fn_name) g) /\
  ^raw_point gn ti t /\ active_inst gn ti t /\ ti.inst_opcode = INVOKE /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  gas_cut n vs (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^raw_point gn j (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (`f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
     simp[ld_image_def] >>
     Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  drule_all ld_active_lookup >> disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `X = [inst] /\ h = 0 /\ ti = inst /\ t0 = t` by suspend "singleton" >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`X = [inst]`, `h = 0`, `ti = inst`, `t0 = t`] >>
  drule_all ld_invoke_success >>
  disch_then (qx_choosel_then [`nm`,`ops`,`calleeT`,`argsT`,`ct`,`rt`,`uc`] strip_assume_tac) >>
  `gas_cut n vs uc /\ gas_cut n vs s` by suspend "cut" >>
  `taint_ok fn tn inst s` by
    (drule ld_sync_source >> strip_tac >>
     fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  drule completed_callee_first_fetch >>
  disch_then strip_assume_tac >>
  `ld_global lo A (f::fs)` by fs[] >>
  drule_all (BETA_RULE ld_focus_invoke_active_entry) >>
  disch_then (qx_choosel_then [`callee`,`argsS`,`cs`,`saved`,`fc`,`PG1`,`tn1`,`ic`,`Y`]
    (map_every assume_tac o CONJUNCTS)) >>
  `ld_return_cont C callee cs cs` by suspend "continuation" >>
  suspend "return"
QED

Resume ld_focus_raw_completed_invoke[singleton]:
  drule ld_sync_source >> strip_tac >>
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

Resume ld_focus_raw_completed_invoke[cut]:
  `u.vs_gas_readings = uc.vs_gas_readings` by
    (drule gas_bind_outputs_readings >> simp[]) >>
  conj_tac >- fs[gas_cut_def] >>
  `ct.vs_gas_readings = s.vs_gas_readings` by
    (drule gas_setup_callee_readings >> simp[]) >>
  `LENGTH uc.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`calleeT`,`ct`] mp_tac (cj 3 gas_count_suffix) >>
     simp[gas_count_suffix_def] >> disch_then SUBST1_TAC >> simp[LENGTH_DROP]) >>
  pop_assum mp_tac >>
  qpat_x_assum `gas_cut n vs (u with vs_inst_idx := _)` mp_tac >>
  simp[gas_cut_def] >> decide_tac
QED

Resume ld_focus_raw_completed_invoke[continuation]:
  `ALL_DISTINCT (MAP (\b. b.bb_label) callee.fn_blocks)` by
    (`MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `o1_fn_shape C callee` by (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
     drule o1_fn_shape_components >> simp[]) >>
  `cs.vs_current_bb = ct.vs_current_bb` by
    (drule_all ld_focus_invoke_correlated_setup >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  `lower_dload_function_supply (Sigma nm) callee =
     (calleeT, SND (lower_dload_function_supply (Sigma nm) callee))` by
    metis_tac[pairTheory.PAIR] >>
  drule_all ld_setup_active_entry >> strip_tac >>
  irule ld_return_cont_entry >> simp[]
QED

Resume ld_focus_raw_completed_invoke[return]:
  `lookup_block t.vs_current_bb gn.fn_blocks = SOME bb` by
    (drule o1LowerDloadRunnerBoundaryTheory.ld_invoke_bind_control >> strip_tac >> fs[]) >>
  `calleeT = ld_image fc` by simp[ld_image_def] >>
  Q.SUBGOAL_THEN `?sf rs cs' Ar fr tnr rinst se te PGr Gr Nr.
    run_blocks sf C callee cs = IntRet rs cs' /\
    ld_sync lo P C vs (saved::stk) PGr Gr tnr callee rinst se te Ar fr Nr /\
    ^ld_probe_stable lo P Sigma names (f::fs) fc A Ar fr /\
    rinst.inst_opcode = RET /\
    step_inst 0 C rinst se = IntRet rs cs' /\
    step_inst 0 C' rinst te = IntRet rt uc /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo Ar tnr cs' uc /\ ld_nonghost tnr cs' uc /\
    (!a. a IN ld_slots Ar (f::fs) ==>
      FLOOKUP (DRESTRICT Ar (ld_slots Ar (f::fs))) a = FLOOKUP Ar a) /\
    cs'.vs_gas_readings = uc.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH cs'.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) fr`
    (assume_tac o BETA_RULE) >-
    (BETA_TAC >> irule (BETA_RULE ld_focus_successful_return) >>
     rpt conj_tac >> simp[]
     >- (goal_assum (drule_at (Pat `eval_phis _ _ = OK _`)) >>
         goal_assum (drule_at (Pat `run_blocks _ _ _ _ = IntRet _ _`)) >>
         reverse conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`PG1`,`FEMPTY`,`tn1`,`ic`,`cs`,`ct`,`A`,`fc::f::fs`,
                       `SUC N`,`Y`,`0`] >>
         `cp'.vs_current_bb = ct.vs_current_bb /\
          cp'.vs_gas_readings = ct.vs_gas_readings` by
           (qpat_assum `(_ with vs_inst_idx := _) = ct`
              (fn th => simp[NoAsms, GSYM th])) >>
         qpat_x_assum `saved = _` SUBST_ALL_TAC >>
         qpat_assum `!g. MEM g (f::fs) ==> _`
           (assume_tac o REWRITE_RULE [MEM]) >>
         qpat_assum `cp'.vs_current_bb = _` SUBST1_TAC >>
         qpat_assum `cp'.vs_gas_readings = _` SUBST1_TAC >>
         qpat_assum `fc.lf_serial = N` mp_tac >>
         rewrite_tac[HD, TL, NOT_CONS_NIL] >>
         strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`D`,`n`] >> simp[]) >>
  qpat_x_assum `saved = _` SUBST_ALL_TAC >>
  drule_all (BETA_RULE ld_focus_invoke_pop_correlated) >>
  disch_then (qx_choosel_then
    [`PG2`,`G2`,`tn2`,`inst1`,`s1`,`t1`,`A1`,`frames1`,`N1`,`Y1`,`p1`,`h1`]
    (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `frames1` >- fs[] >>
  rename1 `ld_sync lo P C vs stk PG2 G2 tn2 fn inst1 s1 t1 A1 (f1::fs1) N1` >>
  `fs1 = fs` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_assum `ld_envelope (HD (f1::fs)).lf_supply _ _ _ _ _`
    (assume_tac o REWRITE_RULE [HD]) >>
  `t1.vs_inst_idx = p1` by
    (qpat_x_assum `ld_sync _ _ _ _ stk _ _ _ _ inst s t _ _ _` kall_tac >>
     drule_all ld_sync_envelope_position >> simp[]) >>
  `h1 < LENGTH Y1` by metis_tac[ld_prefix_bound] >>
  `j = EL h1 Y1` by
    (qpat_assum `ld_prefix C' gn Y1 p1 h1 t1 _`
       (assume_tac o MATCH_MP ld_prefix_active) >>
     `ALL_DISTINCT (fn_labels gn)` by (rewrite_tac[fn_labels_def] >> first_assum ACCEPT_TAC) >>
     irule fmpStageBlockSimCodeTheory.active_inst_unique >>
     goal_assum (drule_at (Pat `active_inst _ j _`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`stk`,`PG2`,`G2`,`tn2`,`fn`,`inst1`,`s1`,`t1`,`A1`,
                `f1`,`fs`,`N1`,`Y1`,`p1`,`h1`] >>
  qpat_assum `gn = ld_image (HD (f1::fs))` (assume_tac o REWRITE_RULE [HD]) >>
  rewrite_tac[HD, TL, NOT_CONS_NIL] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ld_focus_raw_completed_invoke

(* Bounded LowerDload coverage on the actual raw reachability derivation. *)
Theory gasFocusLowerDloadRawSafety
Ancestors
  gasFocusLowerDloadRawPointSafety gasFocusLowerDloadRawCompletedInvoke
  gasFocusLowerDloadRoot gasFocusLowerDloadControlEntry gasFocusLowerDloadCallEntry
  gasFocusLowerDloadCutGuards gasFocusLowerDloadEnvironmentPoint
  gasFocusLowerDloadArithmeticBindingPoint gasFocusLowerDloadLogStorePoint
  gasFocusLowerDloadScratchNext gasFocusLowerDloadBytesWrite gasFocusLowerDloadBytesNext
  lowerDloadReturnStable lowerDloadOracleCallAssembly venomInstProps
  lowerDloadOwnedForwarding lowerDloadOwnedTransitionBoundary lowerDloadEnvelopeControl
  lowerDloadReturnInterior lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadPtrStatic lowerDloadExpansionEndpoint lowerDloadReturnAlignment
  lowerDloadForwardingCoverage lowerDloadSafetyLocations lowerDloadReachability venomWf
  lowerDloadSafetyAmbient o1LowerDloadRunnerBoundary
  lowerDloadClassifiedReadPointEffect lowerDloadSafetyAdvance lowerDloadSafetyAllocBounds
  lowerDloadSafetyKeyedEnvironmentReadEffects lowerDloadSafetyAccountReadEffects
  lowerDloadSafetyStorageReadEffects lowerDloadSafetyValues lowerDloadSafetyUpdates
  memLocDefs pointerConfinedDefs lowerDloadSafetyHashLog lowerDloadSafetyImmutableWriteEffects
  lowerDloadSafetyTaintWidth lowerDloadSafetyDelegate lowerDloadSafetyCreate
  lowerDloadMemoryWritePointEffect lowerDloadPublicCopyPointEffect lowerDloadOrdinaryEndpoint
  gasCount venomEffects lowerDloadFrontier ctxLookupAgree lowerDloadDefs codegenRel
  fmpStageBlockSimCode contextRawReachable o1SafeUpto o1PassContract
  o1ContractLowerDload venomExecSemantics venomInst venomState finite_map list
Libs lowerDloadReturnPackageLib lowerDloadForwardingPackageLib

val raw_point = ``\gn ti t.
  ?stk PG G tn fn inst s t0 A f fs N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
    gn = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
    t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\ h < LENGTH X /\
    ti = EL h X /\ s.vs_gas_readings = t0.vs_gas_readings /\
    t0.vs_gas_readings = t.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)``;

val raw_forward = ``\gn ti t. ^ld_forward C' gn ti t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)``;

Theorem ld_focus_raw_successor[local]:
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) /\ ld_global lo Ar (g::fs) /\
  gn = ld_image f /\ gn = FST (lower_dload_function_supply f.lf_supply fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH X /\
  ss.vs_current_bb = s.vs_current_bb /\ active_inst gn j q /\
  g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\ g.lf_tgt = q /\
  ss.vs_gas_readings = q.vs_gas_readings /\
  LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs /\
  (!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG G tn fn ni g.lf_src g.lf_tgt Ar (g::fs) N) ==>
  ^raw_point gn j q
Proof
  strip_tac >>
  `^ld_probe_stable lo P Sigma names fs f A Ar (g::fs)` by
    (irule ld_stable_head_extend >> metis_tac[]) >>
  drule_all ld_envelope_successor_head >> strip_tac >>
  `active_inst fn next g.lf_src` by simp[] >>
  `ld_sync lo P C vs stk PG G tn fn next g.lf_src g.lf_tgt Ar (g::fs) N` by
    metis_tac[] >>
  qpat_x_assum `(\lo P Sigma names fs f A0 A frames. _) lo P Sigma names fs f A Ar (g::fs)`
    (strip_assume_tac o BETA_RULE) >>
  BETA_TAC >> qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`next`,`g.lf_src`,`q`,
    `Ar`,`g`,`fs`,`N`,`Y`,`p+LENGTH X`,`0`] >>
  gvs[ld_image_def, ld_prefix_zero, EVERY_MEM] >>
  rpt strip_tac
  >- metis_tac[] >>
  irule (arithmeticTheory.LESS_EQ_TRANS) >>
  qexists_tac `LENGTH s.vs_gas_readings` >>
  metis_tac[]
QED

Theorem ld_focus_raw_ordinary_effect[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  o1_ctx_shape C /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  gn = ld_image f /\ gn = FST (lower_dload_function_supply f.lf_supply fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\ step_inst fuel C inst s = OK ss /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss u /\
  ld_nonghost (step_taint inst s ss tn) ss u /\
  ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
  ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  s.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs ==>
  ^raw_point gn j (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>` >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[] >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` by
    simp[Abbr `q`, arithmeticTheory.ADD1] >>
  `?i Y. active_inst fn i s1 /\
    ld_envelope f.lf_supply fn s1 (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`gn`] mp_tac) >>
     simp[Abbr `s1`, arithmeticTheory.ADD1, Excl "EL"] >> metis_tac[]) >>
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST [`f` |->
       `f with <|lf_src := ss; lf_tgt := u; lf_H := H'; lf_tv := (step_taint inst s ss tn).t_var|>`,
       `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr `g`, Abbr `s1`, Abbr `q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn i s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[markerTheory.Abbrev_def]) >>
  `ss.vs_gas_readings = q.vs_gas_readings` by fs[ld_nonghost_def, Abbr `q`] >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP, Abbr `q`] >> decide_tac) >>
  `!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn ni g.lf_src g.lf_tgt A (g::fs) N` by
    (`g.lf_src = s1 /\ g.lf_tgt = q` by simp[Abbr `g`] >>
     rpt strip_tac >>
     `ni = i` by metis_tac[REWRITE_RULE[venomInstTheory.fn_labels_def] active_inst_unique] >>
     simp[]) >>
  qpat_assum `^ld_probe_stable lo P Sigma names fs f A A (f::fs)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `^raw_point gn j q` by
    (BETA_TAC >> irule (BETA_RULE ld_focus_raw_successor) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`[inst]`,`f`,`fn`,
               `fs`,`g`,`t.vs_inst_idx`,`s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
     simp[Abbr `g`, Abbr `s1`] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[]
QED

Theorem ld_focus_actual_raw_safety:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo n C vs ==>
  !fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C' fn inst s /\ dload_offset_ok C' fn inst s /\
    dload_headroom_ok C' fn inst s
Proof
  strip_tac >> drule_all ld_focus_stage_suppliers >> strip_tac >>
  `EVERY pre_fmp_ops C.ctx_functions` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def, fmp_free_ctx_def, EVERY_MEM] >>
  `ctx_has_dalloca C' ==> ctx_has_dalloca C` by
    metis_tac[lower_dload_stage_no_dalloca] >>
  `!v ctx gn ti t. raw_reachable v ctx gn ti t ==>
    v = vs /\ ctx = C' /\ gas_cut n vs t ==>
    ^raw_point gn ti t \/ ^raw_forward gn ti t` suffices_by
    (disch_then (qspec_then `vs` (qspec_then `C'` (assume_tac o BETA_RULE))) >>
     rpt gen_tac >> strip_tac >>
     irule (BETA_RULE ld_focus_raw_point_safety) >>
     qexistsl [`C`,`D`,`P`,`Sigma`,`lo`,`n`,`names`,`rpolicy`,`view`,`vs`] >>
     simp[]) >>
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume ld_focus_actual_raw_safety[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >> disj1_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >> simp[EVERY_MEM] >>
     disch_then irule >> metis_tac[lookup_function_MEM]) >>
  drule_all_then (qspecl_then [`lo`,`C'`] strip_assume_tac)
    (SRULE [] (Q.INST [`fn'` |-> `FST (lower_dload_function_supply u fn)`]
      ld_focus_root_correlated)) >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  BETA_TAC >>
  qexistsl [`[]`,`[]`,`FEMPTY`,`entry_taint`,`fn`,`inst`,`t`,`t`,`FEMPTY`,
    `f`,`[]`,`1`,`X`,`0`] >>
  simp[ld_image_def] >> metis_tac[ld_envelope_active_head]
QED

Resume ld_focus_actual_raw_safety[next]:
  rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
                (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  rename1 `active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx)` >>
  `gas_cut n vs t` by
    (irule ld_step_ok_cut_back >> fs[gas_cut_def] >> metis_tac[]) >>
  qpat_x_assum `_ /\ _ /\ _ ==> _ \/ _` mp_tac >>
  simp[] >> disch_then (DISJ_CASES_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac) o BETA_RULE)
  >- suspend "next_point"
  >> disj2_tac >> BETA_TAC >> conj_tac
  >- (drule_all (BETA_RULE ld_forward_next) >> simp[])
  >> first_assum ACCEPT_TAC
QED

Resume ld_focus_actual_raw_safety[block]:
  rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
                (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  rename1 `step_inst fuel C' ti t = OK u` >>
  `gas_cut n vs t` by (irule ld_block_entry_cut_back >> metis_tac[]) >>
  qpat_x_assum `_ /\ _ /\ _ ==> _ \/ _` mp_tac >>
  simp[] >> disch_then (DISJ_CASES_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac) o BETA_RULE)
  >- suspend "block_point"
  >> drule_all (BETA_RULE ld_forward_no_terminator_ok) >> metis_tac[]
QED

Resume ld_focus_actual_raw_safety[callee]:
  rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
                (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  rename1 `setup_callee callee args t = SOME cs` >>
  `gas_cut n vs t` by (irule ld_callee_entry_cut_back >> metis_tac[]) >>
  qpat_x_assum `_ /\ _ /\ _ ==> _ \/ _` mp_tac >>
  simp[] >> disch_then (DISJ_CASES_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac) o BETA_RULE)
  >- suspend "callee_point"
  >> drule (BETA_RULE ld_forward_no_invoke) >> simp[]
QED

Resume ld_focus_actual_raw_safety[block_point]:
  pop_assum strip_assume_tac >>
  rename1 `ld_sync lo P C vs stk PG G tn source inst s t0 A (f::fs) N` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) source.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  drule ld_sync_source >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     drule_all ld_envelope_nonterminal >> strip_tac >>
     fs[EVERY_EL] >> metis_tac[]) >>
  drule_all ld_envelope_ordinary >> strip_tac >>
  `h = 0` by fs[] >>
  `t0 = t /\ ti = inst` by fs[ld_prefix_zero] >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  drule_all ld_terminator_ok_branch >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `raw_reachable vs C source inst s` by metis_tac[ld_frame_reachable_raw] >>
  qpat_assum `o1_safe_upto _ _ _ _ _` (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def]) >>
  `raw_mem_ok C source inst s /\ dload_offset_ok C source inst s` by metis_tac[] >>
  qpat_x_assum `o1_ptr_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_ptr_safe_upto_def, ptr_discipline_upto_def]) >>
  `taint_ok source tn inst s` by metis_tac[] >>
  `gn = FST (lower_dload_function_supply (Sigma source.fn_name) source)` by
    (drule ld_sync_head >> strip_tac >> fs[ld_image_def]) >>
  qpat_x_assum `inst = EL h X` kall_tac >>
  rename1 `enters_block gn u tp` >> rename1 `active_inst gn j tp` >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any (qspecl_then [`j`,`tp`,`u`,`names`,`fuel`,`gn`,`Sigma`,`C'`] mp_tac)
      ld_focus_control_entry) >>
  (impl_tac >- (simp[NoAsms] >> rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, fs[MEM], metis_tac[]])) >>
  strip_tac >> disj1_tac >>
  qexistsl [`stk`,`PG`,`G'`,`entry_taint_vars source (jump_to lbl' s) tn`,
    `source`,`ni`,`s1`,`tp`,`A`,`g`,`fs`,`N`,`X'`,`0`] >>
  qpat_assum `(\lo P Sigma names fs f0 A0 A frames. _) lo P Sigma names fs f A A (g::fs)`
    (strip_assume_tac o BETA_RULE) >>
  qpat_assum `EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\ _) (g::fs)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `0 < LENGTH X'` by metis_tac[ld_prefix_bound] >>
  simp[] >>
  qpat_assum `!k. MEM k fs ==> FRANGE k.lf_H SUBSET _ /\ _`
    (mp_tac) >> metis_tac[]
QED

Resume ld_focus_actual_raw_safety[callee_point]:
  pop_assum strip_assume_tac >>
  rename1 `ld_sync lo P C vs stk PG G tn source inst s t0 A (f::fs) N` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) source.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  drule ld_sync_source >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     drule_all ld_envelope_nonterminal >>
     rewrite_tac[EVERY_EL] >> disch_then (qspec_then `h` mp_tac) >> gvs[]) >>
  drule_all ld_envelope_ordinary >> strip_tac >>
  `h = 0` by fs[] >>
  `t0 = t /\ ti = inst` by fs[ld_prefix_zero] >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`X = [inst]`, `h = 0`, `ti = inst`, `t0 = t`] >>
  `taint_ok source tn inst s` by
    (`gas_cut n vs s` by fs[gas_cut_def] >>
     fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  `!g. MEM g C.ctx_functions ==> lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))` by metis_tac[] >>
  `EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)` by simp[] >>
  `^ld_probe_stable lo P Sigma names fs f A A (f::fs)` by
    (simp[] >> metis_tac[]) >>
  drule_all ld_focus_invoke_active_entry >>
  disch_then (qx_choosel_then [`calleeS`,`argsS`,`csS`,`saved`,`fc`,`PG1`,`tn1`,`ic`,`Y`]
    (map_every assume_tac o CONJUNCTS)) >>
  `callee = ld_image fc` by simp[ld_image_def] >>
  `0 < LENGTH Y` by metis_tac[ld_prefix_bound] >>
  qpat_x_assum `inst = EL 0 [inst]` kall_tac >>
  qpat_x_assum `(\lo P Sigma names fs f0 A0 A frames. _) lo P Sigma names (f::fs) fc A A (fc::f::fs)`
    (strip_assume_tac o BETA_RULE) >>
  disj1_tac >>
  qexistsl [`saved::stk`,`PG1`,`FEMPTY`,`tn1`,`calleeS`,`ic`,`csS`,`cs`,`A`,
    `fc`,`f::fs`,`SUC N`,`Y`,`0`] >> fs[] >> metis_tac[]
QED

Resume ld_focus_actual_raw_safety[next_point]:
  Cases_on `ti.inst_opcode = INVOKE`
  >- (disj1_tac >>
      mp_tac (BETA_RULE ld_focus_raw_completed_invoke) >>
      simp[NoAsms] >> (impl_tac >- (rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, metis_tac[]])) >> simp[CONJ_ASSOC]) >>
  qpat_x_assum `?stk PG G tn fn' inst s t0 A f fs N X h. _` strip_assume_tac >>
  rename1 `ld_sync lo P C vs stk PG G tn source inst s t0 A (f::fs) N` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) source.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  drule ld_sync_source >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    ((metis_tac[ld_envelope_source_nonterminal])) >>
  Cases_on `SUC h < LENGTH X`
  >- suspend "interior" >>
  `SUC h = LENGTH X` by decide_tac >>
  suspend "endpoint"
QED

Resume ld_focus_actual_raw_safety[interior]:
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) X` by
    (drule_all ld_envelope_nonterminal >> simp[EVERY_MEM]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[ld_prefix_control, ld_sync_control] >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `t.vs_inst_idx = t0.vs_inst_idx + h` by metis_tac[ld_prefix_position] >>
  `gn = FST (lower_dload_function_supply f.lf_supply source)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `active_inst gn (EL (SUC h) X) q` by
    (simp[Abbr `q`] >> irule ld_envelope_target_at >>
     simp[] >> qexistsl [`s.vs_inst_idx`,`t0.vs_inst_idx`,`s`] >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels gn)` by
    (Cases_on `lower_dload_function_supply f.lf_supply source` >>
     drule lower_dload_function_supply_labels >> fs[fn_labels_def]) >>
  `j = EL (SUC h) X` by metis_tac[active_inst_unique] >>
  `step_inst 0 C' (EL h X) t = OK u` by
    metis_tac[step_inst_non_invoke] >>
  `ld_prefix C' gn X t0.vs_inst_idx (SUC h) t0 q` by
    (qpat_x_assum `Abbrev (q = _)` (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     metis_tac[ld_prefix_next]) >>
  `q.vs_gas_readings = t0.vs_gas_readings` by metis_tac[ld_expansion_prefix_readings] >>
  disj1_tac >> qexistsl [`stk`,`PG`,`G`,`tn`,`source`,`inst`,`s`,`t0`,
    `A`,`f`,`fs`,`N`,`X`,`SUC h`] >>
  `u.vs_gas_readings = t0.vs_gas_readings` by
    ((qpat_assum `q.vs_gas_readings = _` mp_tac >> simp[Abbr `q`] >> (gvs[]))) >>
  simp[Abbr `q`] >> metis_tac[]
QED

Resume ld_focus_actual_raw_safety[endpoint]:
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `raw_reachable vs C source inst s` by metis_tac[ld_frame_reachable_raw] >>
  qpat_assum `o1_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def]) >>
  `raw_mem_ok C source inst s /\ dload_offset_ok C source inst s` by metis_tac[] >>
  `dload_headroom_ok C source inst s` by metis_tac[ld_sync_source_mem_inv] >>
  `EVERY inst_wf (fn_insts source)` by
    (drule_all ld_sync_fn_shape >>
     metis_tac[o1_fn_shape_components, fmpStepStructuralTheory.fn_inst_wf_fn_insts]) >>
  `ir_supply_covers_fn f.lf_supply source` by
    (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_sync_supply_covered >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  `gn = FST (lower_dload_function_supply f.lf_supply source)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (Cases_on `lower_dload_function_supply f.lf_supply source` >>
     drule lower_dload_function_supply_labels >> fs[fn_labels_def]) >>
  Cases_on `in_revert_forward source s`
  >- (`^ld_forward C' gn ti t` by
        (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
          (BETA_RULE ld_selected_forwarding) >>
         simp[HD] >> metis_tac[]) >>
      pop_assum (assume_tac o BETA_RULE) >>
      disj2_tac >> BETA_TAC >> conj_tac
      >- (drule_all (BETA_RULE ld_forward_next) >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  `inst_wf inst` by
    metis_tac[EVERY_MEM, ld_active_inst_member] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) X` by
    (drule_all ld_envelope_nonterminal >> simp[EVERY_MEM]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[ld_prefix_control, ld_sync_control] >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `^ld_probe_stable lo P Sigma names fs f A A (f::fs)` by
    (simp[] >> metis_tac[]) >>
  disj1_tac >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- suspend "dload" >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- suspend "bytes" >>
  suspend "singleton"
QED

Resume ld_focus_actual_raw_safety[dload]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    (fs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `ld_prefix C' (ld_image f) X t0.vs_inst_idx h t0 t /\
   step_inst fuel C' (EL h X) t = OK u` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`p` |-> `t0.vs_inst_idx`]
    (SPEC_ALL ld_focus_dload_scratch_next))) >> strip_tac >>
  `ss.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  qabbrev_tac `g = f with
    <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx;
      lf_H := set_prov f.lf_H [out] NONE;
      lf_E := inst.inst_id INSERT f.lf_E;
      lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `^raw_point gn j (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (BETA_TAC >> irule (BETA_RULE ld_focus_raw_successor) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`X`,`f`,`source`,
               `fs`,`g`,`t0.vs_inst_idx`,`s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
     simp[Abbr `g`] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[]
QED

Resume ld_focus_actual_raw_safety[bytes]:
  `?dest off len. inst.inst_operands = [dest;off;len]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `LENGTH X = 2` by
    (drule_all lowerDloadPublicTraceTheory.ld_dloadbytes_envelope_temporary >>
     strip_tac >> simp[]) >>
  `h = 1` by decide_tac >>
  `ld_prefix C' gn X t0.vs_inst_idx 1 t0 t /\
   step_inst fuel C' (EL 1 X) t = OK u` by metis_tac[] >>
  drule_all (REWRITE_RULE [] (Q.INST [`p` |-> `t0.vs_inst_idx`]
    (SPEC_ALL ld_focus_bytes_classified_write))) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `lo <= vs.vs_alloca_next` by fs[o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
  drule_all (REWRITE_RULE [LET_THM] (Q.INST [`p` |-> `t0.vs_inst_idx`]
    (SPEC_ALL ld_focus_bytes_classified_next))) >>
  disch_then (strip_assume_tac o BETA_RULE) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  qpat_x_assum `t = (update_var _ _ _ with vs_inst_idx := _)` kall_tac >>
  qpat_x_assum `ss = write_memory_with_expansion _ _ _` kall_tac >>
  qpat_x_assum `u = write_memory_with_expansion _ _ _` kall_tac >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >>
  qpat_x_assum `step_prov _ _ _ _ = _` kall_tac >>
  qabbrev_tac `g = f with
    <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx|>` >>
  `^raw_point gn j (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (BETA_TAC >> irule (BETA_RULE ld_focus_raw_successor) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`X`,`f`,`source`,
               `fs`,`g`,`t0.vs_inst_idx`,`s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
     simp[Abbr `g`] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[]
QED

Resume ld_focus_actual_raw_safety[singleton]:
  `X = [inst]` by metis_tac[ld_envelope_ordinary] >>
  `h = 0` by fs[] >>
  `t = t0 /\ ti = inst` by fs[ld_prefix_zero] >>
  `?bb. lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst` by
    (qpat_assum `active_inst gn ti t`
       (strip_assume_tac o REWRITE_RULE[contextCodegenRelTheory.active_inst_def]) >>
     qexists_tac `bb` >> simp[get_instruction_def] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  `ld_sync lo P C vs stk PG G tn source inst s t A (f::fs) N /\
   ld_envelope f.lf_supply source s s.vs_inst_idx [inst] t.vs_inst_idx /\
   step_inst fuel C' inst t = OK u /\
   active_inst (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[] >>
  `EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)` by simp[] >>
  Cases_on `MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE]`
  >- (suspend "singleton_environment") >>
  Cases_on `MEM inst.inst_opcode
    [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;
     NOT;SIGNEXTEND;BYTE;OFFSET;ADD;SUB;SHL;SHR;SAR] \/
    MEM inst.inst_opcode [ASSIGN;RETPC_PARAM;PARAM]`
  >- (suspend "singleton_scalar") >>
  Cases_on `MEM inst.inst_opcode [LOG;SSTORE;TSTORE]`
  >- (suspend "singleton_log_store") >>
  suspend "singleton_residual"
QED

fun pack_singleton th =
  strip_assume_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] th)) >>
  `ld_image g = ld_image f` by simp[ld_image_def] >>
  `gn = ld_image g` by metis_tac[] >>
  qpat_x_assum `g = _` kall_tac >>
  qpat_x_assum `t = t0` (SUBST_ALL_TAC o SYM) >>
  map_every (fn pat => qpat_assum pat (strip_assume_tac o SIMP_RULE (srw_ss()) [EVERY_DEF]))
    [`EVERY (\a. a.lf_src.vs_gas_readings = _ /\ _) (g::fs)`,
     `EVERY (\a. a.lf_supply = _) (g::fs)`,
     `EVERY (\a. !j b. _) (g::fs)`] >>
  qexistsl [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,
    `source`,`i`,`ss with vs_inst_idx := SUC s.vs_inst_idx`,
    `u with vs_inst_idx := SUC t.vs_inst_idx`,`A`,`g`,`fs`,`N`,`Y`,`0`] >>
  simp[] >> conj_tac
  >- (qpat_assum `!a. MEM a fs ==> FRANGE a.lf_H SUBSET _ /\ _`
        (fn th => POP_ASSUM_LIST (K (mp_tac th))) >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `ld_prefix _ (ld_image g) Y _ 0 _ _`
        (mp_tac o SIMP_RULE (srw_ss()) []) >> simp[]) >>
  qpat_assum `(ss with vs_inst_idx := SUC s.vs_inst_idx).vs_gas_readings = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings`
    (SUBST_ALL_TAC o SYM) >> simp[];

Resume ld_focus_actual_raw_safety[singleton_environment]:
  `t.vs_inst_idx = t.vs_inst_idx` by simp[] >>
  drule_all ld_focus_environment_point_next >> disch_then pack_singleton
QED

Resume ld_focus_actual_raw_safety[singleton_scalar]:
  `t.vs_inst_idx = t.vs_inst_idx` by simp[] >>
  drule_all (CONV_RULE (REWR_CONV LET_THM THENC BETA_CONV)
    ld_focus_arithmetic_binding_point_next) >>
  disch_then pack_singleton
QED

Resume ld_focus_actual_raw_safety[singleton_log_store]:
  `t.vs_inst_idx = t.vs_inst_idx` by simp[] >>
  drule_all ld_focus_log_store_point_next >> disch_then pack_singleton
QED

Resume ld_focus_actual_raw_safety[singleton_residual]:
  qpat_x_assum `t = t0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  `MEM inst (fn_insts source)` by metis_tac[ld_active_inst_member] >>
  `MEM source C.ctx_functions` by metis_tac[ld_sync_head] >>
  `pre_fmp_ops source` by fs[EVERY_MEM] >>
  `ld_global lo A (f::fs)` by simp[] >>
  `s.vs_gas_readings = t.vs_gas_readings` by metis_tac[] >>
  qpat_assum `o1_ptr_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_ptr_safe_upto_def]) >>
  `lo <= vs.vs_alloca_next` by fs[ptr_discipline_upto_def] >>
  drule_all concretizeLayoutCutSafeTheory.ptr_discipline_upto_at >> strip_tac >>
  `lo <= dyn_floor C vs /\ t.vs_alloca_next <= dyn_floor C vs /\
   t.vs_alloca_next < dimword(:256) /\
   (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
      b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs /\ c+sz < dimword(:256))` by
    (drule_all lowerDloadDynHeadroomTheory.ld_raw_dyn_headroom >> strip_tac >>
     drule ld_raw_reachable_frontier >> strip_tac >>
     drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ source inst s t _ _ _`) ld_sync_frontier >> strip_tac >>
     `t.vs_alloca_next <= dyn_floor C vs` by decide_tac >>
     `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_target_headroom] >>
     `lo <= dyn_floor C vs` by decide_tac >> simp[] >>
     drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ source inst s t _ _ _`) ld_sync_slots >> strip_tac >>
     drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ source inst s t _ _ _`) ld_sync_maps >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     drule_all ld_alloc_frontiers >> simp[] >> decide_tac) >>
  `ld_image f = FST (lower_dload_function_supply (Sigma source.fn_name) source)` by
    (qpat_assum `gn = ld_image f` (rewrite_tac o single o GSYM) >>
     qpat_assum `gn = FST _` SUBST1_TAC >>
     qpat_assum `f.lf_supply = _` SUBST1_TAC >>
     qpat_assum `f.lf_fn = source` SUBST1_TAC >> REFL_TAC) >>
  Cases_on `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]`
  >- suspend "singleton_read" >>
  Cases_on `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]`
  >- suspend "singleton_write" >>
  Cases_on `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
  >- suspend "singleton_copy" >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- suspend "singleton_dalloca" >>
  suspend "singleton_residual_other"
QED

Resume ld_focus_actual_raw_safety[singleton_read]:
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `(MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward source s)` by
    (disch_tac >> qpat_assum `~in_revert_forward source s` ACCEPT_TAC) >>
  drule_all ld_sync_classified_read_effect_at >> strip_tac >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >>
     qpat_assum `inst.inst_opcode = _` (fn eq =>
       simp[NoAsms, eq, is_alloca_op_def, write_effects_def, empty_effects_def,
            source_memory_write_ranges_def])) >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_write]:
  `fn_shape_ok source /\ fn_inst_wf source` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  drule_all ld_sync_memory_write_effect_at >> strip_tac >>
  `ld_ghost_ok (dyn_floor C vs) A f.lf_H (step_prov PG G inst ss)` by
    (qpat_assum `step_prov PG G inst ss = G` (rewrite_tac o single) >>
     drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ source inst s t _ _ _`) ld_sync_ghosts >>
     simp[NoAsms, HD]) >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H;
       lf_tv := (step_taint inst s ss tn).t_var|>)` by
    (qpat_assum `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_tv := _|>)`
       mp_tac >> simp[NoAsms, ld_vars_def]) >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_copy]:
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
       b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  drule_all ld_sync_public_copy_effect_at >> strip_tac >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_dalloca]:
  `ctx_has_dalloca C` by
    (simp[NoAsms, ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  `w2n vs.vs_initial_fmp <= w2n s.vs_fmp` by
    (qpat_assum `frame_reachable vs C _ _ _ _ source inst s`
       (mp_tac o MATCH_MP ptrDisciplineEmptyTaintTheory.frame_reachable_initial_fmp) >>
     strip_tac >>
     qpat_assum `ctx_has_dalloca C ==> allocas_below_fmp s` mp_tac >>
     qpat_assum `s.vs_initial_fmp = vs.vs_initial_fmp` mp_tac >>
     qpat_assum `ctx_has_dalloca C` mp_tac >>
     rpt strip_tac >> fs[allocas_below_fmp_def]) >>
  drule_all ld_sync_dalloca_effect_at >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_residual_other]:
  Cases_on `inst.inst_opcode = ALLOCA`
  >- suspend "singleton_alloca" >>
  suspend "singleton_data_external"
QED

Resume ld_focus_actual_raw_safety[singleton_alloca]:
  `?out. inst.inst_outputs = [out]` by
    (qpat_assum `inst_wf inst` mp_tac >>
     qpat_assum `inst.inst_opcode = ALLOCA` mp_tac >>
     simp[NoAsms, inst_wf_def, LENGTH_EQ_NUM_compute] >>
     metis_tac[NoAsms]) >>
  `MEM out (fn_ir_vars source)` by
    (irule lowerDloadSafetyUpdatesTheory.ld_inst_output_ir >> qexists_tac `inst` >> simp[]) >>
  `out IN fn_pv P source` by
    (mp_tac (Q.INST [`fn` |-> `source`] o1LowerDloadClosureTheory.ptr_roots_subset_fn_pv) >>
     simp[pred_setTheory.SUBSET_DEF, ptr_roots_def, pointerConfinedDefsTheory.alloca_roots_def] >>
     disch_then irule >> disj1_tac >> disj1_tac >> qexists_tac `inst` >>
     simp[inst_output_def]) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- suspend "singleton_fresh" >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME allocation` >>
  PairCases_on `allocation` >>
  suspend "singleton_cached"
QED

Resume ld_focus_actual_raw_safety[singleton_cached]:
  `t.vs_inst_idx = t.vs_inst_idx` by simp[] >>
  drule_all lowerDloadSafetyAllocationTheory.ld_cached_alloca_endpoint >> strip_tac >>
  `ss.vs_current_bb = s.vs_current_bb /\ ss.vs_gas_readings = s.vs_gas_readings` by
    (qpat_assum `step_inst 0 C inst s = OK ss` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas inst.inst_id = SOME _` mp_tac >>
     qpat_assum `inst.inst_opcode = ALLOCA` mp_tac >>
     qpat_assum `inst.inst_outputs = [out]` mp_tac >>
     simp[NoAsms, lowerDloadSafetyAllocationTheory.ld_alloca_step,
          exec_alloca_def, update_var_def] >>
     rpt strip_tac >> qpat_assum `_ = ss` (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by
    (qpat_assum `ld_nonghost _ ss u` mp_tac >> simp[NoAsms, ld_nonghost_def]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms, arithmeticTheory.ADD1]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply source)` by
    (qpat_assum `f.lf_fn = source` mp_tac >> simp[NoAsms, ld_image_def]) >>
  `^raw_point (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx)` suffices_by
    (qpat_assum `ld_image f = FST (lower_dload_function_supply (Sigma _) _)`
       (fn th => simp[NoAsms, th])) >>
  BETA_TAC >> irule (BETA_RULE ld_focus_raw_successor) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`[inst]`,`f`,`source`,
    `fs`,`g`,`t.vs_inst_idx`,`s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
  simp[NoAsms, GSYM arithmeticTheory.ADD1] >>
  conj_tac >- (qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` (rewrite_tac o single) >> simp[NoAsms]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ld_focus_actual_raw_safety[singleton_fresh]:
  drule_all lowerDloadSafetyAllocationTheory.ld_sync_original_site_fresh >> strip_tac >>
  mp_tac (lowerDloadSafetyAllocationTheory.ld_fresh_alloca_dispatch |> Q.INST
    [`s` |-> `s`, `t` |-> `t`, `inst` |-> `inst`, `out` |-> `out`,
     `fuel` |-> `fuel`, `C'` |-> `C'`, `ts` |-> `u`]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sz` (qx_choose_then `ss` strip_assume_tac)) >>
  `step_inst 0 C inst s = OK ss` by
    (qpat_assum `step_inst fuel C inst s = OK ss` mp_tac >>
     qpat_assum `inst.inst_opcode = ALLOCA` mp_tac >>
     simp[NoAsms, lowerDloadSafetyAllocationTheory.ld_alloca_step]) >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `ss.vs_current_bb = s.vs_current_bb /\ ss.vs_memory = s.vs_memory /\
   u.vs_memory = t.vs_memory /\ ss.vs_gas_readings = s.vs_gas_readings /\
   u.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `ss = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `u = update_var _ _ _` SUBST1_TAC >> simp[NoAsms, update_var_def]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply source)` by
    (qpat_assum `f.lf_fn = source` mp_tac >> simp[NoAsms, ld_image_def]) >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = SUC t.vs_inst_idx` by
    (qpat_assum `u.vs_current_bb = s.vs_current_bb` mp_tac >> simp[NoAsms, Abbr `q`]) >>
  `q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` by simp[arithmeticTheory.ADD1] >>
  `?i Y. active_inst source i sn /\
         ld_envelope f.lf_supply source sn sn.vs_inst_idx Y q.vs_inst_idx` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)) >>
     qexistsl [`i`,`Y`] >>
     `sn = ss with vs_inst_idx := SUC s.vs_inst_idx` by simp[NoAsms, Abbr `sn`] >>
     qpat_assum `q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` SUBST1_TAC >>
     qpat_assum `sn = _` SUBST1_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ld_envelope _ _ (ss with vs_inst_idx := _) _ Y _` mp_tac >>
     simp[NoAsms]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      source i sn` by
    (simp[NoAsms, Abbr `sn`] >> irule frame_reachable_next >>
     metis_tac[]) >>
  suspend "singleton_fresh_update"
QED

Resume ld_focus_actual_raw_safety[singleton_fresh_update]:
  qabbrev_tac `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz))` >>
  qabbrev_tac `H' = f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
  qabbrev_tac `tn' = step_taint inst s ss tn` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[NoAsms] >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[NoAsms, pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
     irule ld_global_selected >> qexistsl [`f`,`f::fs`,`lo`] >> simp[]) >>
  `step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase Ar o_f H' /\
   ld_vars P Ar (f with <|lf_src := ss; lf_tgt := u; lf_H := H'; lf_tv := tn'.t_var|>) /\
   ld_memory lo Ar tn' ss u /\ ld_nonghost tn' ss u /\ FRANGE H' SUBSET FDOM Ar` by
    (`Ar = A |+ ((f.lf_serial,inst.inst_id),
                  (s.vs_alloca_next,t.vs_alloca_next,w2n sz))` by simp[NoAsms, Abbr `Ar`] >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_fn = source` (SUBST_ALL_TAC o SYM) >>
     drule_all lowerDloadSafetyAllocationTheory.ld_fresh_alloca_effect >>
     disch_then (qspecl_then [`0`,`PG`,`C'`,`C`] strip_assume_tac) >>
     qpat_assum `Abbrev (H' = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (tn' = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ld_vars P Ar g` by
    (qpat_assum `ld_vars P Ar _` mp_tac >>
     simp[NoAsms, Abbr `g`, Abbr `sn`, Abbr `q`, ld_vars_def]) >>
  `ld_memory lo Ar tn' sn q /\ ld_nonghost tn' sn q` by
    (conj_tac
     >- (qpat_assum `ld_memory lo Ar tn' ss u` mp_tac >>
         simp[NoAsms, Abbr `sn`, Abbr `q`, ld_memory_def] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `ld_nonghost tn' ss u` mp_tac >>
     simp[NoAsms, Abbr `sn`, Abbr `q`, ld_nonghost_def] >>
     strip_tac >> rpt conj_tac >> metis_tac[]) >>
  `ld_ghost_ok (dyn_floor C vs) Ar H' (step_prov PG G inst ss)` by
    (`~MEM inst.inst_opcode [PARAM; ADD; SUB; ASSIGN]` by
       (qpat_assum `inst.inst_opcode = ALLOCA` (rewrite_tac o single) >> simp[NoAsms]) >>
     drule_then irule ld_ghost_ok_step_fixed >> metis_tac[]) >>
  suspend "singleton_fresh_pack"
QED

Resume ld_focus_actual_raw_safety[singleton_fresh_pack]:
  `source_memory_write_ranges inst s = []` by
    (qpat_assum `inst.inst_opcode = ALLOCA` (fn th =>
       simp[NoAsms, th, source_memory_write_ranges_def])) >>
  `ld_dyn_agree (dyn_floor C vs) tn'.t_mem sn.vs_memory q.vs_memory` by
    (simp[NoAsms, Abbr `sn`, Abbr `q`, Abbr `tn'`] >>
     drule ld_sync_dyn_agree >> strip_tac >>
     drule_all ld_dyn_agree_unwritten >> disch_then ACCEPT_TAC) >>
  `lo <= s.vs_alloca_next /\ lo <= t.vs_alloca_next` by
    (drule ld_raw_reachable_frontier >> strip_tac >>
     drule ld_sync_frontier >> decide_tac) >>
  `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
   sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\
   q = u with vs_inst_idx := SUC t.vs_inst_idx /\
   g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` by
    simp[NoAsms, Abbr `Ar`, Abbr `sn`, Abbr `q`, Abbr `g`] >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' source i sn q Ar (g::fs) N /\
   ld_global lo Ar (g::fs)` by
    (drule_all (SRULE [PULL_EXISTS] lowerDloadSafetyAllocationTheory.ld_sync_fresh_alloca_update) >>
     qpat_assum `g = _` SUBST1_TAC >> qpat_assum `sn = _` SUBST1_TAC >>
     qpat_assum `q = _` SUBST1_TAC >> qpat_assum `Ar = _` SUBST1_TAC >>
     disch_then ACCEPT_TAC) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = sn /\ g.lf_tgt = q` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms]) >>
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by
    (qpat_assum `Ar = _` SUBST1_TAC >> simp[NoAsms, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ss.vs_gas_readings = q.vs_gas_readings` by
    (qpat_assum `q = _` SUBST1_TAC >> simp[NoAsms] >> metis_tac[]) >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` (rewrite_tac o single) >> simp[NoAsms]) >>
  `!ni. active_inst source ni g.lf_src ==>
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' source ni g.lf_src g.lf_tgt Ar (g::fs) N` by
    (qpat_assum `g.lf_src = sn` SUBST1_TAC >> qpat_assum `g.lf_tgt = q` SUBST1_TAC >>
     rpt strip_tac >>
     `ni = i` by metis_tac[REWRITE_RULE[venomInstTheory.fn_labels_def] active_inst_unique] >>
     qpat_assum `ni = i` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `^raw_point (ld_image f) j q` suffices_by
    (qpat_assum `ld_image f = FST (lower_dload_function_supply (Sigma _) _)`
       (fn th => simp[NoAsms, th]) >>
     qpat_assum `q = _` SUBST1_TAC >> simp[NoAsms]) >>
  BETA_TAC >> irule (BETA_RULE ld_focus_raw_successor) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`A`,`Ar`,`step_prov PG G inst ss`,`N`,`PG`,`[inst]`,`f`,`source`,
    `fs`,`g`,`t.vs_inst_idx`,`s`,`ss`,`stk`,`tn'`] >>
  `g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  simp[NoAsms, GSYM arithmeticTheory.ADD1] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ld_focus_actual_raw_safety[singleton_data_external]:
  `pre_fmp_opcode inst.inst_opcode` by fs[pre_fmp_ops_def, EVERY_MEM] >>
  `fn_ptr_ok P source` by metis_tac[ld_sync_ptr_ok] >>
  `inst.inst_opcode <> MEMTOP` by fs[fn_ptr_ok_def] >>
  `step_inst_base inst t = OK u` by metis_tac[step_inst_non_invoke] >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >> qpat_assum `step_inst_base inst t = OK u` mp_tac >>
     simp[NoAsms, step_inst_base_def] >>
     qpat_assum `inst.inst_opcode = PHI` (rewrite_tac o single) >>
     simp[NoAsms, opcode_case_def]) >>
  `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3] \/
   MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] \/
   MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;SELFBALANCE;
                         EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD]` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`pre_fmp_opcode inst.inst_opcode`, `~is_terminator inst.inst_opcode`,
        `inst.inst_opcode <> PHI`, `inst.inst_opcode <> MEMTOP`,
        `inst.inst_opcode <> INVOKE`, `inst.inst_opcode <> DLOAD`,
        `inst.inst_opcode <> DLOADBYTES`, `inst.inst_opcode <> ALLOCA`,
        `inst.inst_opcode <> DALLOCA`, `~MEM inst.inst_opcode (CALLER::_)`,
        `~(MEM inst.inst_opcode (MUL::_) \/ MEM inst.inst_opcode _)`,
        `~MEM inst.inst_opcode (LOG::_)`, `~MEM inst.inst_opcode (MLOAD::_)`,
        `~MEM inst.inst_opcode (MSTORE::_)`, `~MEM inst.inst_opcode (CODECOPY::_)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `inst.inst_opcode` >> simp[pre_fmp_opcode_def, is_terminator_def])
  >- suspend "singleton_data"
  >- suspend "singleton_external"
  >> suspend "singleton_obs_read"
QED

Resume ld_focus_actual_raw_safety[singleton_obs_read]:
  `fn_shape_ok source` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  drule ld_sync_memory >> strip_tac >>
  `?ss. step_inst_base inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (`tn.t_var = f.lf_tv` by metis_tac[] >>
     qpat_assum `f.lf_fn = source` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     let
       fun finish effect =
         drule_all effect >>
         disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`
           (qx_choose_then `ss` strip_assume_tac)) >>
         qexists_tac `ss` >> rpt conj_tac >> first_assum ACCEPT_TAC
     in
       Cases_on `MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD]`
       >- finish ld_keyed_environment_read_effect >>
       Cases_on `MEM inst.inst_opcode [BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH]`
       >- finish ld_account_read_effect >>
       `MEM inst.inst_opcode [SLOAD;TLOAD]` by
         (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
          qpat_assum `~MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
          qpat_assum `~MEM inst.inst_opcode (BALANCE::_)` mp_tac >>
          pure_rewrite_tac[MEM] >> metis_tac[NoAsms]) >>
       finish ld_storage_read_effect
     end) >>
  `step_inst fuel C inst s = OK ss` by simp[step_inst_non_invoke] >>
  qpat_assum `ld_erase A o_f set_prov _ _ NONE = _` (assume_tac o SYM) >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  `!a. a IN FRANGE (set_prov f.lf_H inst.inst_outputs NONE) ==> a IN FDOM A` by
    (rpt strip_tac >>
     drule (SRULE [pred_setTheory.SUBSET_DEF]
       (Q.INST [`q` |-> `NONE`] lowerDloadSafetyUpdatesTheory.ld_set_prov_range)) >>
     simp[] >> metis_tac[ld_global_selected, MEM]) >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >>
     qpat_assum `inst.inst_opcode = _` (fn eq =>
       simp[NoAsms, eq, is_alloca_op_def, write_effects_def, empty_effects_def,
            source_memory_write_ranges_def])) >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_data]:
  `fn_shape_ok source` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `tn.t_var = f.lf_tv` by metis_tac[] >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[NoAsms, HD] >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by metis_tac[ld_global_selected, MEM] >>
  Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
  >- suspend "singleton_identity" >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- suspend "singleton_istore" >>
  suspend "singleton_sha3"
QED

Resume ld_focus_actual_raw_safety[singleton_identity]:
  `inst.inst_outputs = []` by
    (qpat_assum `MEM inst.inst_opcode (NOP::_)` (strip_assume_tac o REWRITE_RULE[MEM]) >>
     fs[inst_wf_def]) >>
  `eval_operands inst.inst_operands s = eval_operands inst.inst_operands t` by
    (`!v. MEM (Var v) inst.inst_operands ==>
        MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn` by
       (qpat_assum `f.lf_fn = source` SUBST1_TAC >>
        gen_tac >> strip_tac >> conj_tac
        >- metis_tac[ld_inst_input_ir] >>
        irule ld_ptr_use_scalar >> simp[Excl "MEM"] >> qexists_tac `inst` >>
        qpat_assum `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
          (strip_assume_tac o REWRITE_RULE[MEM]) >>
        qpat_assum `inst.inst_opcode = _` (fn eq =>
          simp[NoAsms, eq, mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `~MEM inst.inst_opcode
       [ASSIGN;PHI;RET;RETFMP;DRET;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by
       (qpat_assum `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
          (strip_assume_tac o REWRITE_RULE[MEM]) >> simp[]) >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_fn = source` (SUBST_ALL_TAC o SYM) >>
     drule_all ld_vars_numeric_operands_equal >> simp[NoAsms]) >>
  `u = t /\ step_inst_base inst s = OK s` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`eval_operands inst.inst_operands s = _`, `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`] >>
     qpat_assum `step_inst_base inst t = OK u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_tac >> disch_then (strip_assume_tac o REWRITE_RULE[MEM]) >> disch_tac >>
     qpat_assum `step_inst_base inst t = OK u` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >> simp[Once step_inst_base_def] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
     gvs[eval_operands_def, AllCaseEqs()] >> simp[Once step_inst_base_def] >>
     gvs[AllCaseEqs()]) >>
  `step_taint inst s s tn = tn /\ step_prov PG G inst s = G` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`inst.inst_outputs = []`, `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE[MEM]) >> disch_tac >>
     simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
          written_taint_def, new_site_bytes_def, step_writes_def,
          source_memory_write_ranges_def, range_bytes_def, set_var_taint_def,
          store_taint_def, adopt_reset_def, imm_taint_def,
          taint_component_equality, FLOOKUP_DEF, DRESTRICT_UNIV, SF CONJ_ss] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
     Cases_on `t` >> simp[] >> pred_setLib.SET_TAC[]) >>
  `step_inst fuel C inst s = OK s` by simp[step_inst_non_invoke] >>
  `ld_vars P A (f with <|lf_src := s; lf_tgt := u; lf_H := f.lf_H;
            lf_tv := (step_taint inst s s tn).t_var|>)` by
    (map_every (fn q => qpat_assum q (rewrite_tac o single))
       [`u = t`, `step_taint inst s s tn = tn`, `f.lf_src = s`,
        `f.lf_tgt = t`, `f.lf_tv = tn.t_var`] >>
     qpat_assum `f.lf_src = s` (rewrite_tac o single o SYM) >>
     qpat_assum `f.lf_tgt = t` (rewrite_tac o single o SYM) >>
     qpat_assum `f.lf_tv = tn.t_var` (rewrite_tac o single o SYM) >>
     simp[NoAsms, ld_frame_component_equality] >> first_assum ACCEPT_TAC) >>
  `ld_memory lo A (step_taint inst s s tn) s u /\
   ld_nonghost (step_taint inst s s tn) s u /\
   ld_ghost_ok (dyn_floor C vs) A f.lf_H (step_prov PG G inst s) /\
   ld_dyn_agree (dyn_floor C vs) (step_taint inst s s tn).t_mem s.vs_memory u.vs_memory /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (map_every (fn q => qpat_assum q (rewrite_tac o single))
       [`u = t`, `step_taint inst s s tn = tn`, `step_prov PG G inst s = G`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `^raw_point (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (BETA_TAC >> irule (BETA_RULE ld_focus_raw_ordinary_effect) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`A`,`G`,`f.lf_H`,`N`,`PG`,`f`,`source`,`fs`,`fuel`,`inst`,`s`,`s`,`stk`,`tn`] >>
     simp[NoAsms] >> rpt conj_tac >> metis_tac[]) >>
  pop_assum mp_tac >> simp[]
QED

Resume ld_focus_actual_raw_safety[singleton_istore]:
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
      b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  `?ss. step_inst_base inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f f.lf_H /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (qpat_assum `f.lf_fn = source` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
     drule_all ld_write2_operands >> strip_tac >>
     rename1 `inst.inst_operands = [addr; value]` >>
     `!oper. MEM oper inst.inst_operands ==> op_prov f.lf_H oper = NONE` by
       (rpt strip_tac >> Cases_on `oper` >> simp[NoAsms, op_prov_def] >>
        irule ld_vars_unselected >> qexistsl [`A`,`P`] >>
        reverse conj_tac >- first_assum ACCEPT_TAC >>
        qpat_assum `fn_ptr_ok P f.lf_fn` mp_tac >> simp[NoAsms, fn_ptr_ok_def] >>
        metis_tac[]) >>
     `op_prov f.lf_H addr = NONE /\ op_prov f.lf_H value = NONE` by simp[] >>
     `word_agree_except (op_taint tn value) x y` by
       (irule ld_write_scalar_observation >> qexistsl [`A`,`P`,`f`,`inst`] >>
        qpat_assum `inst.inst_opcode = ISTORE` (rewrite_tac o single) >>
        qpat_assum `inst.inst_operands = [addr;value]` (rewrite_tac o single) >>
        simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `op_taint tn addr = {}` by metis_tac[ld_write2_taint] >>
     `dst = dst'` by
       (irule (cj 1 ld_write_address_observation) >>
        qexistsl [`A`,`P`,`f`,`inst`,`addr`,`tn`] >>
        qpat_assum `inst.inst_opcode = ISTORE` (rewrite_tac o single) >>
        qpat_assum `inst.inst_operands = [addr;value]` (rewrite_tac o single) >>
        simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `dst = dst'` (SUBST_ALL_TAC o SYM) >>
     `?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = addr` by
       simp[mem_write_ops_def] >>
     `MEM (w2n dst,32) (source_memory_write_ranges inst f.lf_src)` by
       (qpat_assum `inst.inst_opcode = ISTORE` (fn opcode =>
        qpat_assum `inst.inst_operands = [addr;value]` (fn operands =>
          simp[NoAsms, source_memory_write_ranges_def, opcode, operands]) >>
        simp[fixed_source_write_range_def])) >>
     `0 < (32:num)` by simp[] >>
     `(op_prov f.lf_H ops.iao_ofst = NONE ==> dst = dst) /\
      (!k. op_prov f.lf_H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) dst dst)` by simp[] >>
     (Q.SUBGOAL_THEN
       `w2n dst+32 <= lo \/
        (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
          w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz) \/
        dyn_floor C vs <= w2n dst` assume_tac
      >- (drule_all (Q.INST [`n` |-> `32`] (cj 2 ld_access_dyn_cases)) >> metis_tac[])) >>
     `op_taint tn value SUBSET {j | j < 32}` by metis_tac[ld_reachable_op_taint_width] >>
     drule_all ld_istore_effect >> disch_then (qx_choose_then `ss` strip_assume_tac) >>
     qexists_tac `ss` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `step_inst fuel C inst s = OK ss` by simp[step_inst_non_invoke] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H;
       lf_tv := (step_taint inst s ss tn).t_var|>)` by
    (qpat_assum `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_tv := _|>)`
       mp_tac >> simp[NoAsms, ld_vars_def]) >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_sha3]:
  `inst.inst_opcode = SHA3` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3]`,
        `~MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`, `inst.inst_opcode <> ISTORE`] >>
     simp[NoAsms, MEM] >> metis_tac[NoAsms]) >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `?ss. step_inst_base inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (qpat_assum `f.lf_fn = source` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     drule_all ld_sha3_operands >> strip_tac >>
     drule_all ld_sha3_effect >>
     disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`
       (qx_choose_then `ss` strip_assume_tac)) >>
     qexists_tac `ss` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `step_inst fuel C inst s = OK ss` by simp[step_inst_non_invoke] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  `!a. a IN FRANGE (set_prov f.lf_H inst.inst_outputs NONE) ==> a IN FDOM A` by
    (rpt strip_tac >>
     drule (SRULE [pred_setTheory.SUBSET_DEF]
       (Q.INST [`q` |-> `NONE`] lowerDloadSafetyUpdatesTheory.ld_set_prov_range)) >>
     simp[] >> metis_tac[ld_global_selected, MEM]) >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `inst.inst_opcode = SHA3` (fn eq =>
       simp[NoAsms, eq, is_alloca_op_def, write_effects_def, empty_effects_def,
            source_memory_write_ranges_def])) >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Resume ld_focus_actual_raw_safety[singleton_external]:
  `fn_shape_ok source` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `tn.t_var = f.lf_tv` by metis_tac[] >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[NoAsms, HD] >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  `!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v` by
    metis_tac[ld_alloc_bounds] >>
  `!a k u v z b c sz. FLOOKUP A a = SOME (u,v,z) /\
    FLOOKUP A k = SOME (b,c,sz) /\ a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)` by
    metis_tac[ld_alloc_separate] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
      b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `?ss. step_inst_base inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (qpat_assum `f.lf_fn = source` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     Cases_on `MEM inst.inst_opcode [CALL;STATICCALL]`
     >- ((Q.SUBGOAL_THEN
           `?g a v ao az ro rz st.
             (inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
               st = f.lf_tgt.vs_call_ctx.cc_static) \/
             (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)`
           (REPEAT_TCL CHOOSE_THEN assume_tac)
          >- (qpat_assum `inst_wf inst` mp_tac >>
              qpat_assum `MEM inst.inst_opcode [CALL;STATICCALL]` mp_tac >>
              pure_rewrite_tac[MEM] >> strip_tac >>
              qpat_assum `inst.inst_opcode = _` (fn th =>
                simp[NoAsms, th, inst_wf_def, LENGTH_EQ_NUM_compute]) >>
              disch_tac >> metis_tac[])) >>
         drule_all ld_oracle_call_step >> strip_tac >>
         qexists_tac `ss` >> (metis_tac[ld_oracle_call_provenance])) >>
     Cases_on `inst.inst_opcode = DELEGATECALL`
     >- (drule_all ld_delegate_step >> strip_tac >>
         `step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
            (ld_erase A o_f f.lf_H) inst ss =
          ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE` by
           (qpat_assum `inst.inst_opcode = DELEGATECALL` (fn opcode =>
             simp[NoAsms, opcode, step_prov_def, out_prov_def, ld_erase_set_prov])) >>
         qexists_tac `ss` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `MEM inst.inst_opcode [CREATE;CREATE2]` by
       (qpat_assum `MEM inst.inst_opcode (CALL::_)` mp_tac >>
        qpat_assum `~MEM inst.inst_opcode [CALL;STATICCALL]` mp_tac >>
        pure_rewrite_tac[MEM] >> metis_tac[]) >>
     drule_all ld_create_step >>
     disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
     `ld_dyn_agree (dyn_floor C vs) (step_taint inst f.lf_src ss tn).t_mem ss.vs_memory u.vs_memory` by
       (qpat_assum `(step_taint inst f.lf_src ss tn).t_mem = tn.t_mem` (rewrite_tac o single) >>
        qpat_assum `ss.vs_memory = f.lf_src.vs_memory` (rewrite_tac o single) >>
        qpat_assum `u.vs_memory = f.lf_tgt.vs_memory` (rewrite_tac o single) >>
        first_assum ACCEPT_TAC) >>
     qexists_tac `ss` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `step_inst fuel C inst s = OK ss` by simp[step_inst_non_invoke] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  `!a. a IN FRANGE (set_prov f.lf_H inst.inst_outputs NONE) ==> a IN FDOM A` by
    (rpt strip_tac >>
     drule (SRULE [pred_setTheory.SUBSET_DEF]
       (Q.INST [`q` |-> `NONE`] lowerDloadSafetyUpdatesTheory.ld_set_prov_range)) >>
     simp[] >> metis_tac[ld_global_selected, MEM]) >>
  drule_all (SIMP_RULE (srw_ss()) [] ld_focus_raw_ordinary_effect) >>
  qpat_assum `ld_image f = FST _` (rewrite_tac o single)
QED

Finalise ld_focus_actual_raw_safety

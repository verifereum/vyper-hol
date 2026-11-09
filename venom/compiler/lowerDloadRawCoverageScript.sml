(* Exhaustive raw target-prefix coverage. *)
Theory lowerDloadRawCoverage
Ancestors
  lowerDloadStageAmbient lowerDloadOwnedTransitions lowerDloadOwnedCalls
  lowerDloadOwnedTransitionBoundary lowerDloadLiveAllocation list contextCodegenRel
  lowerDloadOwnedForwarding lowerDloadCurrentSafety contextRawReachable
  lowerDloadForwardingCoverage lowerDloadExpansionEndpoint venomWf lowerDloadReturnAlignment
  o1PassContract unitMemInv venomInst venomExecSemantics o1LowerDloadRunnerBoundary
  lowerDloadSafetyKernel lowerDloadSafetyLocations o1ContractLowerDload venomExecProps lowerDloadEnvelopeControl
Libs
  lowerDloadOwnedTransitionPackageLib lowerDloadReturnPackageLib
  lowerDloadForwardingPackageLib
Theorem ld_raw_fixed_ambient:
  (!fn. MEM fn C.ctx_functions ==>
    ^ld_covered_ambient lo C C' vs Sigma names fn
      (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  mem_inv raw_mem_ok C vs ==>
  ?fn. MEM fn C.ctx_functions /\
    ^ld_covered_ambient lo C C' vs Sigma names fn
      (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))
Proof
  strip_tac >>
  `?name fn lbl. C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl` by
    (qpat_x_assum `mem_inv raw_mem_ok C vs` mp_tac >>
     simp[mem_inv_def, codegen_reachability_package_def] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  qexists_tac `fn` >> simp[]
QED

Theorem ld_raw_owned_elim:
  callee_first names C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    ^ld_covered_ambient lo C C' vs Sigma names fn
      (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  ^ld_owned lo P C C' vs Sigma names fn' ti t ==>
  ?stk PG G tn fn inst s t0 A f fs N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
    ^ld_covered_ambient lo C C' vs Sigma names fn fn' /\
    fn' = ld_image f /\
    ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X
Proof
  strip_tac >> fs[] >>
  `frames <> []` by metis_tac[ld_sync_active] >>
  Cases_on `frames` >> fs[] >>
  rename1 `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ (f::fs) _` >>
  `MEM fn C.ctx_functions` by
    (drule ld_sync_source >> strip_tac >>
     drule_all frame_reachable_live_functions >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`f`,`fs`,`N`,`X`,`p`,`h`] >>
  simp[] >> metis_tac[ld_image_def]
QED

Theorem ld_raw_next_closed:
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    ^ld_covered_ambient lo C C' vs Sigma names fn
      (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  mem_inv raw_mem_ok C vs /\
  (^ld_owned lo P C C' vs Sigma names fn' ti t \/
   (^ld_forward C' fn' ti t /\
    ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks))) /\
  ~is_terminator ti.inst_opcode /\ step_inst fuel C' ti t = OK u /\
  active_inst fn' next (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_owned lo P C C' vs Sigma names fn' next
      (u with vs_inst_idx := SUC t.vs_inst_idx) \/
   (^ld_forward C' fn' next (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)))
Proof
  strip_tac
  >- suspend "owned"
  >> disj2_tac >> conj_tac
  >- (drule_all ld_forward_next >> simp[])
  >> first_assum ACCEPT_TAC
QED

Resume ld_raw_next_closed[owned]:
  drule_all ld_raw_fixed_ambient >> strip_tac >>
  `callee_first names C.ctx_functions /\ o1_ctx_shape C` by fs[] >>
  drule_all ld_raw_owned_elim >> strip_tac >>
  qmatch_goalsub_abbrev_tac `Goal` >>
  rename1 `ld_envelope f.lf_supply source s s.vs_inst_idx X p` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) source.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  `t0.vs_inst_idx = p` by
    (drule_all ld_sync_envelope_position >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (`f.lf_fn = source` by (drule ld_sync_active >> simp[]) >>
     `fn' = FST (lower_dload_function_supply f.lf_supply source)` by
       simp[ld_image_def] >>
     qpat_x_assum `fn' = FST _` (fn th => rewrite_tac[th]) >>
     Cases_on `lower_dload_function_supply f.lf_supply source` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  Cases_on `in_revert_forward source s`
  >- suspend "forward_entry"
  >> Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke"
  >> suspend "ordinary"
QED
Resume ld_raw_next_closed[forward_entry]:
  `^ld_forward C' fn' ti t` by
    (qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' ti t` kall_tac >>
     `EVERY inst_wf (fn_insts source)` by
       (drule_all ld_sync_fn_shape >> strip_tac >>
        drule o1_fn_shape_components >>
        simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_def,
             MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[fn_insts_blocks_MEM]) >>
     `dload_headroom_ok C source inst s` by
       (fs[] >> drule_all ld_sync_source_mem_inv >> simp[]) >>
     `ir_supply_covers_fn f.lf_supply source` by
       (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
          ld_sync_supply_covered >>
        disch_then (qspec_then `Sigma` mp_tac) >>
        (impl_tac >- fs[]) >> simp[]) >>
     drule_all (SRULE [] (Q.INST [`frames` |-> `f::fs`] ld_selected_forwarding)) >> simp[]) >>
  simp[Abbr `Goal`] >> disj2_tac >> simp[] >>
  drule_all ld_forward_next >> simp[]
QED
Resume ld_raw_next_closed[invoke]:
  qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' ti t` kall_tac >>
  `active_inst source inst s` by metis_tac[ld_sync_source] >>
  `X = [inst]` by (irule ld_envelope_ordinary >> simp[] >> metis_tac[]) >>
  `h = 0` by (drule ld_prefix_bound >> simp[]) >>
  gvs[ld_prefix_zero] >>
  qpat_assum `active_inst _ inst t`
    (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
  `lookup_block t.vs_current_bb
     (FST (lower_dload_function_supply (Sigma source.fn_name) source)).fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  qunabbrev_tac `Goal` >> disj1_tac >>
  irule (BETA_RULE ld_owned_invoke_next) >>
  simp[] >>
  goal_assum (drule_at Any) >>
  simp[] >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `!g. MEM g fs ==> _` mp_tac >>
  simp[] >> metis_tac[]
QED
Resume ld_raw_next_closed[ordinary]:
  qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' ti t` kall_tac >>
  `active_inst source inst s` by metis_tac[ld_sync_source] >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `~is_terminator inst.inst_opcode` by
    (Cases_on `inst.inst_opcode = DLOAD` >- simp[is_terminator_def] >>
     Cases_on `inst.inst_opcode = DLOADBYTES` >- simp[is_terminator_def] >>
     `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
     `h = 0` by fs[] >> gvs[]) >>
  Cases_on `SUC h < LENGTH X`
  >- suspend "interior"
  >> `SUC h = LENGTH X` by decide_tac >>
  qunabbrev_tac `Goal` >> disj1_tac >>
  BETA_TAC >> irule (BETA_RULE ld_owned_endpoint_next) >> simp[] >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  gvs[] >>
  qpat_assum `ld_prefix _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `!g. MEM g fs ==> _` mp_tac >> simp[] >> metis_tac[]
QED
Resume ld_raw_next_closed[interior]:
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
    (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ti.inst_opcode <> INVOKE` by (fs[EVERY_EL] >> metis_tac[]) >>
  `step_inst 0 C' (EL h X) t = OK u` by
    (qpat_assum `ti = EL h X` (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `step_inst fuel C' ti t = OK u` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `^ld_owned lo P C C' vs Sigma names fn' (EL (SUC h) X)
     (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (BETA_TAC >> irule (BETA_RULE ld_owned_interior_next) >> simp[] >>
     qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     gvs[] >> qpat_x_assum `!g. MEM g fs ==> _` mp_tac >> simp[] >> metis_tac[]) >>
  suspend "interior_align"
QED
Resume ld_raw_next_closed[interior_align]:
  `active_inst fn' (EL (SUC h) X) (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' (EL (SUC h) X) _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >>
     drule ld_prefix_active >> simp[]) >>
  `next = EL (SUC h) X` by
    (qpat_x_assum `active_inst fn' next _` mp_tac >>
     qpat_x_assum `active_inst fn' (EL (SUC h) X) _` mp_tac >>
     qpat_x_assum `ALL_DISTINCT (MAP _ fn'.fn_blocks)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[active_inst_def] >> rpt strip_tac >>
     `bb = bb'` by (irule ld_block_label_unique >> metis_tac[]) >> gvs[]) >>
  qunabbrev_tac `Goal` >> BETA_TAC >> disj1_tac >>
  qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' (EL (SUC h) X) _`
    (mp_tac o BETA_RULE) >> simp[]
QED
Finalise ld_raw_next_closed


Theorem ld_raw_coverage_fixed:
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    ^ld_covered_ambient lo C C' vs Sigma names fn
      (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  mem_inv raw_mem_ok C vs /\ C'.ctx_entry = C.ctx_entry ==>
  !fn' ti t. raw_reachable vs C' fn' ti t ==>
    (^ld_owned lo P C C' vs Sigma names fn' ti t \/
     ^ld_forward C' fn' ti t)
Proof
  strip_tac >>
  `!v ctx fn' ti t. raw_reachable v ctx fn' ti t ==>
     v = vs /\ ctx = C' ==>
     (^ld_owned lo P C C' vs Sigma names fn' ti t \/
      (^ld_forward C' fn' ti t /\
       ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)))` suffices_by
    (disch_then (qspecl_then [`vs`,`C'`] assume_tac) >>
     rpt gen_tac >> disch_tac >> first_x_assum drule >>
     rewrite_tac[] >> disch_then strip_assume_tac >>
     asm_rewrite_tac[]) >>
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume ld_raw_coverage_fixed[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  disj1_tac >> irule (SRULE [] ld_stage_root_coverage) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume ld_raw_coverage_fixed[next]:
  rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN SUBST_ALL_TAC) >> BETA_TAC >>
  irule (BETA_RULE ld_raw_next_closed) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!fn. MEM fn C.ctx_functions ==> _` mp_tac >> simp[]) >>
  qpat_assum `step_inst fuel C' ti t = OK s'` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `vs = vs /\ C' = C' ==> _`
    (mp_tac o REWRITE_RULE []) >> simp[]
QED

Resume ld_raw_coverage_fixed[block]:
  rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN SUBST_ALL_TAC) >>
  qpat_x_assum `vs = vs /\ C' = C' ==> _`
    (strip_assume_tac o REWRITE_RULE [])
  >- suspend "block_owned"
  >> RULE_ASSUM_TAC BETA_RULE >>
  drule_all (BETA_RULE ld_forward_no_terminator_ok) >>
  disch_then (qspecl_then [`s'`,`fuel`,`C'`] mp_tac) >> simp[]
QED
Resume ld_raw_coverage_fixed[block_owned]:
  drule_all ld_raw_fixed_ambient >> strip_tac >>
  `callee_first names C.ctx_functions /\ o1_ctx_shape C` by fs[] >>
  drule_all ld_raw_owned_elim >> strip_tac >>
  qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' ti t` kall_tac >>
  qmatch_goalsub_abbrev_tac `Goal` >>
  rename1 `ld_envelope f.lf_supply source s s.vs_inst_idx X p` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) source.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  `active_inst source inst s` by metis_tac[ld_sync_source] >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
       (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     fs[EVERY_EL] >> metis_tac[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
  `h = 0` by fs[] >> gvs[ld_prefix_zero] >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    (drule_all ld_terminator_ok_branch >> simp[]) >>
  qunabbrev_tac `Goal` >> BETA_TAC >> disj1_tac >>
  irule (BETA_RULE ld_owned_control_entry) >> simp[] >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `fuel` >> simp[] >>
  conj_tac >- fs[] >>
  qpat_x_assum `!g. MEM g fs ==> _` mp_tac >> simp[] >> metis_tac[]
QED

Resume ld_raw_coverage_fixed[callee]:
  rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN SUBST_ALL_TAC) >>
  qpat_x_assum `vs = vs /\ C' = C' ==> _`
    (strip_assume_tac o REWRITE_RULE [])
  >- suspend "callee_owned"
  >> RULE_ASSUM_TAC BETA_RULE >>
  drule (BETA_RULE ld_forward_no_invoke) >> simp[]
QED
Resume ld_raw_coverage_fixed[callee_owned]:
  drule_all ld_raw_fixed_ambient >> strip_tac >>
  `callee_first names C.ctx_functions /\ o1_ctx_shape C` by fs[] >>
  drule_all ld_raw_owned_elim >> strip_tac >>
  qpat_x_assum `^ld_owned lo P C C' vs Sigma names fn' ti t` kall_tac >>
  qmatch_goalsub_abbrev_tac `Goal` >>
  rename1 `ld_envelope f.lf_supply source s s.vs_inst_idx X p` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) source.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  `active_inst source inst s` by metis_tac[ld_sync_source] >>
  `h < LENGTH X` by metis_tac[ld_prefix_bound] >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X` by
       (irule ld_envelope_nonterminal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     fs[EVERY_EL] >> metis_tac[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
  `h = 0` by fs[] >> gvs[ld_prefix_zero] >>
  `?bb. lookup_block t'.vs_current_bb fn''.fn_blocks = SOME bb` by
    (qpat_x_assum `enters_block fn'' cs t'` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[enters_block_def] >>
     strip_tac >> gvs[] >>
     drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
     strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qunabbrev_tac `Goal` >> BETA_TAC >> disj1_tac >>
  irule (BETA_RULE ld_owned_callee_entry) >> simp[] >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `!g. MEM g fs ==> _` mp_tac >> simp[] >> metis_tac[]
QED
Finalise ld_raw_coverage_fixed

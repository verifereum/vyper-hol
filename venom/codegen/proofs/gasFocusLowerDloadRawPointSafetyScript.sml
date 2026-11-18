(* Read bounded raw safety from the actual correlated LowerDload point. *)
Theory gasFocusLowerDloadRawPointSafety
Ancestors
  gasFocusLowerDloadOrdinarySafety o1SafeUpto lowerDloadTargetHeadroom
  lowerDloadConfiguredOrigins lowerDloadReachability lowerDloadPtrStatic
  lowerDloadReturnAlignment lowerDloadExpansionEndpoint lowerDloadForwardingCoverage
  lowerDloadScratchSafety lowerDloadPublicTrace o1ContractLowerDload
  o1PassContract unitMemInv unitTransformDefs lowerDloadDefs contextRawReachable
  contextCodegenRel codegenRel memSafeRun lowerDloadSafetyKernel
  lowerDloadCurrentSafety lowerDloadSafetyLocations lowerDloadOracleCallAssembly
  frameAllocationOwnership
  venomWf venomExecSemantics venomInst venomState words list
Libs
  lowerDloadReturnPackageLib lowerDloadForwardingPackageLib
  lowerDloadOwnedTransitionPackageLib

Theorem ld_focus_no_dload[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C ==>
  EVERY (\g. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
                    (fn_insts g)) C'.ctx_functions
Proof
  strip_tac >> irule lower_dload_stage_every >>
  qexistsl_tac [`C`, `o1_fn_shape C`, `rpolicy`, `view`] >>
  fs[o1_ctx_shape_def, EVERY_MEM] >>
  rpt strip_tac >> drule_all lower_dload_function_supply_member >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `inst_wf i'` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `EVERY (\j. j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) ys` by
    (qpat_x_assum `inst_wf i'` mp_tac >>
     qpat_x_assum `lower_dload_inst_supply u i' = (ys,v)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `i'.inst_opcode = DLOAD`
     >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
         gvs[lower_dload_inst_supply_def, AllCaseEqs(), instruction_accessors]) >>
     Cases_on `i'.inst_opcode = DLOADBYTES`
     >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
         gvs[lower_dload_inst_supply_def, AllCaseEqs(), instruction_accessors]) >>
     gvs[lower_dload_inst_supply_def]) >> fs[EVERY_MEM]
QED

Theorem ld_focus_revert_opcode[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\ active_inst fn inst s /\
  in_revert_forward fn s ==>
  inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = REVERT
Proof
  strip_tac >> drule_all ld_active_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by simp[get_instruction_def] >>
  gvs[in_revert_forward_def] >> metis_tac[revert_forward_at_opcode]
QED

(* The ADD does not change the destination range or either FMP. At the
   CODECOPY, use just the DLOADBYTES write range already bounded at t0. *)
Theorem ld_focus_bytes_prefix_raw[local]:
  X = [<|inst_id := ai; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [dest; Var z; len]; inst_outputs := []|>] /\
  dest <> Var z /\ len <> Var z /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  raw_mem_ok C fn inst t0 /\ inst_mem_below_frontiers inst t0 /\
  ld_prefix C' gn X p h t0 t ==>
  raw_mem_ok C' gn (EL h X) t
Proof
  strip_tac >> `h < 2` by (drule ld_prefix_bound >> simp[]) >>
  Cases_on `h = 0`
  >- gvs[ld_prefix_zero, raw_mem_ok_def, inst_mem_ok_in_fn_def,
         dalloca_no_wrap_def, inst_mem_below_frontiers_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `h = 1` by decide_tac >> gvs[] >>
  drule_at (Pat `ld_prefix _ _ _ _ _ _ _`) ld_dloadbytes_prefix_observations >>
  simp[] >> strip_tac >>
  `t.vs_fmp = t0.vs_fmp /\ t.vs_initial_fmp = t0.vs_initial_fmp` by
    (dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
     disch_then strip_assume_tac >> gvs[ld_prefix_zero] >>
     qpat_x_assum `step_inst 0 _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
     strip_tac >> gvs[AllCaseEqs(), update_var_def]) >>
  fs[raw_mem_ok_def] >> simp[inst_mem_ok_in_fn_def, dalloca_no_wrap_def] >>
  disj1_tac >>
  fs[inst_mem_below_frontiers_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def]
  >> (gvs[])
QED

Theorem ld_focus_normal_prefix_raw[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  mem_inv dload_headroom_ok C vs /\ ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ir_supply_covers_fn f.lf_supply fn /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ raw_mem_ok C fn inst s /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ t0.vs_inst_idx = p /\
  ld_prefix C' (ld_image f) X p h t0 t ==>
  raw_mem_ok C' (ld_image f) (EL h X) t
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `EVERY inst_wf (fn_insts fn)` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst_wf inst` by metis_tac[ld_active_inst_member, EVERY_MEM] >>
  `w2n t0.vs_initial_fmp <= w2n t0.vs_fmp` by
    (drule ld_sync_memory >> simp[ld_nonghost_def] >> strip_tac >> fs[raw_mem_ok_def]) >>
  Cases_on `inst.inst_opcode = DLOAD` >-
    (`?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
       fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     drule ld_sync_active >> simp[] >> strip_tac >>
     drule_all ld_dload_envelope_temporary >> strip_tac >>
     drule_all ld_sync_dload_scratch_bounds_static >> strip_tac >>
     irule lower_dload_expansion_prefix_raw >>
     goal_assum (drule_at (Pat `ld_prefix _ _ _ _ _ _ _`)) >> metis_tac[]) >>
  Cases_on `in_revert_forward fn s` >-
    (`inst.inst_opcode <> DLOADBYTES /\ inst.inst_opcode <> DALLOCA` by
       (drule_all ld_focus_revert_opcode >> strip_tac >> fs[]) >>
     `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
     `h = 0` by (drule ld_prefix_bound >> simp[]) >> gvs[ld_prefix_zero] >>
     `f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
     `in_revert_forward (ld_image f) t` by
       (irule ld_envelope_revert_forward >> gvs[ld_image_def] >>
        goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
        qexists_tac `SND (lower_dload_function_supply f.lf_supply f.lf_fn)` >>
        simp[] >> metis_tac[ld_sync_control]) >>
     `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
     gvs[raw_mem_ok_def, inst_mem_ok_in_fn_def, in_revert_forward_def,
         dalloca_no_wrap_def]) >>
  drule_all ld_sync_ordinary_raw_pointwise >> strip_tac >>
  Cases_on `inst.inst_opcode = DLOADBYTES` >-
    (`?dest off len. inst.inst_operands = [dest;off;len]` by
       fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
     irule ld_focus_bytes_prefix_raw >>
     goal_assum (drule_at (Pat `ld_prefix _ _ _ _ _ _ _`)) >> metis_tac[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
  `h = 0` by (drule ld_prefix_bound >> simp[]) >>
  gvs[ld_prefix_zero, raw_mem_ok_def, inst_mem_ok_in_fn_def]
QED

Theorem ld_focus_normal_raw_rows[local]:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\
  (!g. MEM g C.ctx_functions ==> ir_supply_covers_fn (Sigma g.fn_name) g) /\
  gas_cut n vs t /\
  (?stk PG G tn fn inst s t0 A f fs N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
    gn = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
    t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\ h < LENGTH X /\
    ti = EL h X /\ s.vs_gas_readings = t0.vs_gas_readings /\
    t0.vs_gas_readings = t.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)) ==>
  raw_mem_ok C' gn ti t /\
  (ctx_has_dalloca C ==> t.vs_alloca_next <= w2n t.vs_initial_fmp)
Proof
  simp[] >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  drule ld_sync_source >> strip_tac >>
  `MEM fn C.ctx_functions /\ raw_reachable vs C fn inst s` by
    metis_tac[frame_reachable_functions_member, ld_frame_reachable_raw] >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
  `ir_supply_covers_fn f.lf_supply fn` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs))` by
    (irule ld_frames_distinct >> qexists_tac `names` >> simp[]) >>
  `mem_inv dload_headroom_ok C vs /\ raw_mem_ok C fn inst s /\
   access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[] >> irule ld_focus_normal_prefix_raw >>
      goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  strip_tac >> irule (BETA_RULE ld_owned_target_headroom_static) >>
  qexistsl_tac [`C`,`C'`,`P`,`Sigma`,`gn`,`lo`,`names`,`ti`,`vs`] >>
  simp[] >> qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`f::fs`,`N`,`X`,`t0.vs_inst_idx`,`h`] >>
  gvs[] >> metis_tac[]
QED

Theorem ld_focus_raw_point_safety:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo n C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  (!g. MEM g C.ctx_functions ==> ir_supply_covers_fn (Sigma g.fn_name) g) /\
  raw_reachable vs C' gn ti t /\ gas_cut n vs t /\
  ((?stk PG G tn fn inst s t0 A f fs N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
    gn = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
    t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\ h < LENGTH X /\
    ti = EL h X /\ s.vs_gas_readings = t0.vs_gas_readings /\
    t0.vs_gas_readings = t.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)) \/
    (^ld_forward C' gn ti t /\ ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks))) ==>
  raw_mem_ok C' gn ti t /\ dload_offset_ok C' gn ti t /\ dload_headroom_ok C' gn ti t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ld_focus_no_dload >> strip_tac >>
  `ctx_dload_count C' = 0` by
    (fs[ctx_dload_count_def, SUM_eq_0, MEM_MAP, PULL_EXISTS,
        FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `MEM gn C'.ctx_functions /\ active_inst gn ti t` by
    (qpat_x_assum `raw_reachable _ _ _ _ _` mp_tac >>
     MAP_EVERY qid_spec_tac [`t`,`ti`,`gn`,`C'`,`vs`] >>
     Induct_on `raw_reachable` >> rw[] >> metis_tac[lookup_function_MEM]) >>
  `MEM ti (fn_insts gn)` by metis_tac[ld_active_inst_member] >>
  `dload_offset_ok C' gn ti t` by
    (fs[dload_offset_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `raw_mem_ok C' gn ti t /\
   (ctx_has_dalloca C' ==> t.vs_alloca_next <= w2n t.vs_initial_fmp)` by
    (qpat_x_assum `_ \/ _` (DISJ_CASES_TAC o BETA_RULE)
     >- (drule_all (BETA_RULE ld_focus_normal_raw_rows) >> strip_tac >>
         simp[] >> metis_tac[lower_dload_stage_no_dalloca]) >>
     conj_tac >- (irule (BETA_RULE ld_forward_current_raw) >> metis_tac[]) >>
     fs[]) >>
  pure_rewrite_tac[dload_headroom_ok_def, GSYM ctx_has_dalloca_def] >>
  fs[raw_mem_ok_def]
QED

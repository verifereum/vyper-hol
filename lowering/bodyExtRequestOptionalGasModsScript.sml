(* The optional generated GAS at the keyword exit reads no source gas. *)
Theory bodyExtRequestOptionalGasMods
Ancestors
  generatedGasOrigin bodyPtrEnvBuiltinsGas bodyPtrEnvBuiltinsEdges
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyForRangeScalarFrameMods bodyFullShadowBodyInv bodyMemBiEnvMsgGas bodyMemoryDefs
  fragGasSeqPtr fragGasOriginPtr bodyPtrDefs ptrDiscipline ptrSafeRun
  gasShadowState gasShadowUnit gasExplicitSites allocaHistory exprLoweringProps
  exprSimWordArgs exprSimProps wordArgsPtr loweringStateRelDefs exprLowering compileEnv
  emitHelper msgGasSim venomInst venomState venomExecSemantics memSafeRun
  finite_map pred_set list codegenRel decoderGhostFramePtr vyperTypeSystem
  unitTransformDefs contextCodegenRel gasOutcomeFullMods gasExemptCertMods
  gasSummary fragGasMode fragGasOrigin fragGasPathMem gasStorage
  vyperStorageTrace vyperStorageFootprint vyperState gasOutcomeFull

Theorem optional_gas_path[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) /\
  (func.fn_name,id) NOTIN explicit /\ ~s.vs_halted /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  gas_prefix 1 s.vs_gas_readings = [w] ==>
  let i = mk_inst id GAS [] [out];
      u = update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings)
  in gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [F]
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G i u,step_taint i s u tn)
Proof
  strip_tac >> simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `step_taint i s u tn` >>
  `step_inst_base i s = OK u /\ ~u.vs_halted` by
    (mp_tac (Q.INST [`id` |-> `id`,`out` |-> `out`] gas_builtin_base_step) >>
     simp[Abbr `i`, Abbr `u`, update_var_def] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_scalar_builtin_at >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn)
     (if i.inst_opcode = GAS then [(func.fn_name,i.inst_id) IN explicit] else [])
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),step_prov PG G i u,step_taint i s u tn)` by
    (irule straight_line_origin_ptr_edge >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          inst_dload_in_section_def, dalloca_no_wrap_def]) >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
  irule_at Any (cj 1 gas_origin_ptr_path_rules) >>
  gvs[Abbr `i`, mk_inst_def]
QED

Theorem optional_gas_stmt_frame[local]:
  stmt_state_rel H ctx func ce cx ke z /\ local_ptrs_reserved ce s3 /\
  ~not_fresh_at s3 (FST (fresh_var s3)) ==>
  stmt_state_rel H ctx func ce cx ke
    (update_var (FST (fresh_var s3)) w (z with vs_gas_readings := readings)
       with vs_inst_idx := idx)
Proof
  strip_tac >>
  `not_local_ptr ce ke.scopes (FST (fresh_var s3))` by
    (simp[fresh_var_def] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `s3` >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ke (update_var (FST (fresh_var s3)) w z)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ (update_var _ _ _)`
    (mp_then Any mp_tac msg_gas_state_frame) >>
  disch_then (qspecl_then [`readings`,`idx`,`ke.gas_obs`] mp_tac) >>
  simp[update_var_def]
QED

Theorem ext_request_optional_gas_mods:
  (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
  (case go of SOME g => (g,h3) | NONE => emit_op GAS [] h3) = (gas,h5) /\
  gas_shadow_state s3 h3 /\ gas_shadow_context ctx shctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code s3 s5 func /\ fn_has_code h3 h5 shfunc /\
  local_ptrs_reserved ce s3 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
  s2.cs_next_var <= s3.cs_next_var /\ ci_mono s3 s5 /\
  alloca_history func z /\ ~z.vs_halted /\
  z.vs_current_bb = s3.cs_current_bb /\ z.vs_inst_idx = LENGTH s3.cs_current_insts /\
  return_buf_frame d ce s3 z /\ wb_frame ce ee ke s2 u z /\
  ghost_kept_at lo ce ee s2 G2 tn2 u G3 tn3 /\
  (!H. valid_horizon cx st0 H ke.storage_trace ==>
    stmt_state_rel H ctx func ce cx ke z /\ immutable_frame_mods func ce cx ke z /\
    storage_well_formed_on cx ke (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ke G3 tn3 z) /\
  (case source_gas of NONE => go = NONE
   | SOME gv => ?op w. go = SOME op /\ eval_operand op z = SOME w /\
       dest_NumV gv = SOME (w2n w) /\ op_taint tn3 op = {}) ==>
  ?zg Gg tng gw n.
    n = (if IS_NONE go then 1 else 0) /\
    (IS_NONE go ==> gas_prefix 1 z.vs_gas_readings = [gw]) /\
    zg.vs_gas_readings = DROP n z.vs_gas_readings /\
    eval_operand gas zg = SOME gw /\ op_taint tng gas = {} /\
    (!k. OPTION_BIND source_gas dest_NumV = SOME k ==> k = w2n gw) /\
    ~zg.vs_halted /\ zg.vs_current_bb = s5.cs_current_bb /\
    zg.vs_inst_idx = LENGTH s5.cs_current_insts /\ alloca_history func zg /\
    zg.vs_memory = z.vs_memory /\ zg.vs_allocas = z.vs_allocas /\
    zg.vs_alloca_next = z.vs_alloca_next /\ zg.vs_fmp = z.vs_fmp /\
    zg.vs_labels = z.vs_labels /\
    tng.t_mem = tn3.t_mem /\ tng.t_stor = tn3.t_stor /\
    tng.t_trans = tn3.t_trans /\ tng.t_imm = tn3.t_imm /\
    (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
      FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
    return_buf_frame d ce s5 zg /\ wb_frame ce ee ke s2 u zg /\
    ghost_kept_at lo ce ee s2 G2 tn2 u Gg tng /\
    (!H. valid_horizon cx st0 H ke.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (z,G3,tn3) (REPLICATE n F) (OK zg,Gg,tng) /\
      stmt_state_rel H ctx func ce cx ke zg /\ immutable_frame_mods func ce cx ke zg /\
      storage_well_formed_on cx ke (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ke Gg tng zg /\
      ghost_kept_at lo ce ke s3 G3 tn3 z Gg tng)
Proof
  Cases_on `go` >> strip_tac >> gvs[]
  >- (Cases_on `source_gas` >> gvs[] >>
      drule_all compile_generated_gas_origin_path >>
      disch_then (qspec_then `T` strip_assume_tac) >>
      qpat_x_assum `gas_origin_path _ _ _ _ _ _ _` kall_tac >>
      `?bb. gas = Var (FST (fresh_var s3)) /\
        s5.cs_current_bb = s3.cs_current_bb /\
        LENGTH s5.cs_current_insts = SUC (LENGTH s3.cs_current_insts) /\
        lookup_block s3.cs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH s3.cs_current_insts) =
          SOME (mk_inst s3.cs_next_id GAS [] [FST (fresh_var s3)])` by
        (qpat_assum `emit_op GAS [] s3 = _` (mp_then Any mp_tac emit_gas_placement_id) >>
         simp[] >> metis_tac[]) >>
      qpat_x_assum `gas = Var out` kall_tac >>
      qpat_x_assum `gas = Var (FST (fresh_var s3))` SUBST_ALL_TAC >>
      qabbrev_tac `out = FST (fresh_var s3)` >>
      qabbrev_tac `i = mk_inst s3.cs_next_id GAS [] [out]` >>
      qabbrev_tac `v = update_var out w (z with vs_gas_readings := DROP 1 z.vs_gas_readings)` >>
      qabbrev_tac `zg = v with vs_inst_idx := LENGTH s5.cs_current_insts` >>
      qabbrev_tac `Gg = step_prov PG G3 i v` >>
      qabbrev_tac `tng = step_taint i z v tn3` >>
      qexistsl [`zg`,`Gg`,`tng`,`w`] >>
      `~not_fresh_at s3 out` by simp[Abbr `out`,fresh_var_def,not_fresh_at_def] >>
      `tng.t_mem = tn3.t_mem` by
        (simp[Abbr `tng`] >> irule step_taint_no_memory_effect >>
         simp[Abbr `i`,Abbr `v`,update_var_def,source_memory_write_ranges_def,
              written_taint_def,mk_inst_def]) >>
      `tng.t_stor = tn3.t_stor /\ tng.t_trans = tn3.t_trans /\ tng.t_imm = tn3.t_imm` by
        (simp[Abbr `tng`] >> irule step_taint_nonmemory_frame >> simp[Abbr `i`,mk_inst_def]) >>
      `compile_env_var MsgGas s3 = (Var out,s5)` by simp[compile_env_var_def] >>
      `alloca_history func zg` by
        (drule_all compile_msg_gas_history >> disch_then (qspec_then `w` mp_tac) >>
         simp[Abbr `zg`,Abbr `v`,update_var_def]) >>
      `!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
        FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)` by
        (rpt strip_tac >> `x <> out` by (strip_tac >> gvs[]) >>
         simp[Abbr `zg`,Abbr `v`,Abbr `Gg`,Abbr `tng`,Abbr `i`,update_var_def,
              lookup_var_def,FLOOKUP_UPDATE,step_prov_other_output,step_taint_other_output,mk_inst_def]) >>
      `eval_operand (Var out) zg = SOME w /\ op_taint tng (Var out) = {}` by
        (conj_tac
         >- simp[Abbr `zg`,Abbr `v`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
         simp[Abbr `tng`, Abbr `i`, scalar_builtin_output_clean]) >>
      `zg.vs_gas_readings = DROP 1 z.vs_gas_readings /\ ~zg.vs_halted /\
       zg.vs_current_bb = s5.cs_current_bb /\ zg.vs_inst_idx = LENGTH s5.cs_current_insts /\
       zg.vs_memory = z.vs_memory /\ zg.vs_allocas = z.vs_allocas /\
       zg.vs_alloca_next = z.vs_alloca_next /\ zg.vs_fmp = z.vs_fmp /\ zg.vs_labels = z.vs_labels` by
        simp[Abbr `zg`,Abbr `v`,update_var_def] >>
      simp[] >> conj_tac
      >- (irule return_buf_frame_frame >> qexistsl [`ce`,`z`,`s3`] >> fs[ci_mono_def]) >>
      conj_tac
      >- (irule wb_frame_readonly_tail >> qexistsl [`s3`,`z`] >> simp[] >> metis_tac[]) >>
      conj_tac
      >- (simp[Abbr `Gg`,Abbr `tng`,Abbr `i`] >> irule single_output_ghost_kept_at >>
          fs[not_fresh_at_def]) >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      conj_tac
      >- (`allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
          drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> disch_tac >>
          `REPLICATE 1 F = [F]` by EVAL_TAC >>
          pop_assum (pure_once_rewrite_tac o single) >>
          `zg = v with vs_inst_idx := SUC z.vs_inst_idx` by simp[Abbr `zg`] >>
          pop_assum (pure_once_rewrite_tac o single) >>
          simp_tac bool_ss [Abbr `Gg`, Abbr `tng`, Abbr `i`, Abbr `v`] >>
          irule (SIMP_RULE bool_ss [LET_THM] optional_gas_path) >> simp[] >>
          qexists_tac `bb` >> simp[]) >>
      conj_tac
      >- (simp_tac bool_ss [Abbr `zg`,Abbr `v`,Abbr `out`] >> irule optional_gas_stmt_frame >> simp[]) >>
      conj_tac
      >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`ke`,`z`,`s3`] >>
          simp[] >> simp[Abbr `zg`,Abbr `v`,update_var_def]) >>
      conj_tac
      >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G3`,`ke`,`z`,`s3`,`tn3`] >>
          simp[] >> simp[Abbr `zg`,Abbr `v`,update_var_def]) >>
      simp[ghost_kept_at_def] >> metis_tac[]) >>
  Cases_on `source_gas` >> gvs[] >>
  qexistsl [`z`,`G3`,`tn3`] >> simp[ghost_kept_at_refl,gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Theorem generated_prefix_exempt_mods[local]:
  gas_path_mem ctx func s0 n (OK s1) /\
  gas_exempt_cert_mods T mods (ctx,func) source (es,s1) marks (err,ee) (leaf,terminal) ==>
  gas_exempt_cert_mods T mods (ctx,func) source (es,s0)
    (REPLICATE n F ++ marks) (err,ee) (leaf,terminal)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0)
     (REPLICATE n F) (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def,gas_marked_path_def,return_def] >>
  drule gas_exempt_cert_start_gas_obs_mods >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_mods_bind_unit >>
  disch_then (qspecl_then [`mods`,`\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

(* The prefix consumes target readings, all marked F. It therefore changes
   neither the observation list replayed by the source nor its entry state. *)
Theorem ext_request_generated_prefix_mods:
  storage_trace_frame source /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) (REPLICATE n F) (OK s1,G1,tn1)) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s1,G1,tn1) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `gas_path_mem ctx func s0 n (OK s1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (drule_then assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `!marks. gas_explicit (REPLICATE n F ++ marks) s0.vs_gas_readings =
     gas_explicit marks s1.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[gas_explicit_append]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `REPLICATE n F ++ marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      qexistsl [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- simp[] >>
      disch_tac >> irule (cj 2 gas_origin_ptr_focus_rules) >>
      qexistsl [`G1`,`s1`,`tn1`] >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      gen_tac >> disch_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
         drule_all storage_trace_frame_prefix >> strip_tac >>
         gvs[] >> drule valid_horizon_append >> simp[]) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
        (drule_then assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (drule_then (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
      qpat_assum `gas_origin_ptr_path _ _ (REPLICATE n F) _`
        (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
      disch_then irule >> simp[])
  >> disj2_tac >> disj2_tac >>
  qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- (irule generated_prefix_exempt_mods >> qexists_tac `s1` >> simp[]) >>
  qexists_tac `H` >> simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- simp[] >>
  disch_tac >> irule (cj 2 gas_origin_ptr_focus_rules) >>
  qexistsl [`G1`,`s1`,`tn1`] >> simp[]
QED

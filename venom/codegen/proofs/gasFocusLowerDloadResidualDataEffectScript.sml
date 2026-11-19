(* Local data effects at a successful singleton LowerDload fetch. *)
Theory gasFocusLowerDloadResidualDataEffect
Ancestors lowerDloadSafetyIdentityCoverage[qualified] lowerDloadSafetyImmutableWriteCoverage[qualified]
  o1SafeUpto gasCount concretizeLayoutCutSafe lowerDloadFrontier ctxLookupAgree
  lowerDloadSafetyHashLog lowerDloadSafetyImmutableWriteEffects
  lowerDloadMemoryWritePointEffect lowerDloadSafetyWriteAssembly
  lowerDloadSafetyTaintWidth lowerDloadOracleCallAssembly
  lowerDloadSafetyAssemblyPremises
  lowerDloadSafetyAllocBounds lowerDloadReturnOrdinary lowerDloadReturnAlignment
  lowerDloadSafetyAmbient lowerDloadSafetyLocations lowerDloadSafetyRelation
  lowerDloadSafetyKernel lowerDloadSafetyValues lowerDloadDefs ptrDiscipline
  memLocDefs pointerConfinedDefs
  o1PassContract codegenRel contextCodegenRelProps venomWf venomEffects
  venomExecProps venomExecSemantics venomInst venomState finite_map pred_set words list
  rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_residual_data_effect:
  o1_ctx_shape C /\ pre_fmp_ops fn /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  ir_supply_covers_fn f.lf_supply fn /\
  MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3;INITIAL_FMP;BUMP] /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ step_inst fuel C' inst t = OK u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem
      ss.vs_memory u.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3]` by
    (qpat_x_assum `pre_fmp_ops fn` mp_tac >> simp[pre_fmp_ops_def, EVERY_MEM] >>
     disch_then (qspec_then `inst` mp_tac) >>
     qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
     simp[MEM, pre_fmp_opcode_def] >> metis_tac[]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >> simp[is_terminator_def]) >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_dyn_agree >> strip_tac >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs s` by
    (irule gas_cut_readings_mono >> qexists_tac `q` >> simp[Abbr `q`]) >>
  `lo <= vs.vs_alloca_next /\ access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (qpat_x_assum `o1_safe_upto _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def, o1_ptr_safe_upto_def,
                                       ptr_discipline_upto_def]) >>
     simp[] >>
     qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ stk PG G tn fn inst s /\ _ ==> _`
       (qspecl_then [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`] mp_tac) >> simp[]) >>
  qpat_x_assum `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3;INITIAL_FMP;BUMP]` kall_tac >>
  Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
  >- suspend "identity" >>
  `lo <= dyn_floor C vs /\ t.vs_alloca_next < dimword(:256) /\
   (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
      b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs /\ c+sz < dimword(:256))` by
    (`mem_inv dload_headroom_ok C vs` by fs[o1_safe_upto_def] >>
     drule_all ld_sync_source_mem_inv >> strip_tac >>
     drule_all ld_frame_raw_reachable >> strip_tac >>
     `s.vs_initial_fmp = vs.vs_initial_fmp` by metis_tac[raw_reachable_initial_fmp] >>
     drule ld_raw_reachable_frontier >> strip_tac >>
     drule ld_sync_frontier >> strip_tac >>
     `t.vs_alloca_next <= dyn_floor C vs` by
       (simp[dyn_floor_def] >> IF_CASES_TAC >>
        gvs[dload_headroom_ok_def, ctx_has_dalloca_def] >> decide_tac) >>
     `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_target_headroom] >>
     `lo <= dyn_floor C vs` by decide_tac >> simp[] >>
     drule ld_sync_slots >> strip_tac >>
     drule ld_sync_maps >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     drule_all ld_alloc_frontiers >> simp[] >> decide_tac) >>
  `~in_revert_forward fn s` by
    (`run_block_non_phis fuel C' bb t = z` by
       (simp[Once run_block_non_phis_def] >> gvs[Abbr `q`]) >>
     `EVERY inst_wf (fn_insts fn)` by
       (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def] >> metis_tac[fn_insts_blocks_MEM]) >>
     `lower_dload_function_supply f.lf_supply fn =
       (ld_image f, SND (lower_dload_function_supply f.lf_supply fn))` by simp[ld_image_def] >>
     `^ld_probe_guard C' fuel bb t` by (BETA_TAC >> metis_tac[]) >>
     irule (Q.INST [`h` |-> `0`, `X` |-> `[inst]`] (BETA_RULE ld_guarded_source_non_revert)) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- suspend "istore" >>
  suspend "sha3"
QED

Resume ld_focus_residual_data_effect[identity]:
  `inst.inst_outputs = []` by
    (qpat_assum `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
       (strip_assume_tac o REWRITE_RULE[MEM]) >>
     qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> strip_tac >> conj_tac
     >- metis_tac[ld_inst_input_ir] >>
     irule ld_ptr_use_scalar >> simp[Excl "MEM"] >> qexists_tac `inst` >>
     gvs[MEM, mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def]) >>
  `~MEM inst.inst_opcode
     [ASSIGN;PHI;RET;RETFMP;DRET;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by
    gvs[MEM] >>
  `eval_operands inst.inst_operands f.lf_src =
   eval_operands inst.inst_operands f.lf_tgt` by
    (irule ld_vars_numeric_operands_equal >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `eval_operands inst.inst_operands s = eval_operands inst.inst_operands t` by
    (qpat_x_assum `eval_operands _ f.lf_src = _` mp_tac >> simp[]) >>
  `step_inst_base inst t = OK u` by
    (qpat_x_assum `step_inst fuel C' inst t = _` mp_tac >> simp[step_inst_non_invoke]) >>
  drule_all lowerDloadSafetyIdentityCoverageTheory.ld_identity_step >> strip_tac >>
  `step_taint inst s s tn = tn /\ step_prov PG G inst s = G` by
    metis_tac[lowerDloadSafetyIdentityCoverageTheory.ld_identity_ghosts] >>
  qexistsl [`s`,`f.lf_H`] >> simp[step_inst_non_invoke] >>
  `f with <|lf_src := s; lf_tgt := t; lf_H := f.lf_H; lf_tv := tn.t_var|> = f` by
    simp[ld_frame_component_equality] >> simp[]
QED

Resume ld_focus_residual_data_effect[istore]:
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
                b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_x_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
  drule_all ld_write2_operands >> strip_tac >>
  rename1 `inst.inst_operands = [addr; value]` >>
  `op_prov f.lf_H addr = NONE /\ op_prov f.lf_H value = NONE` by
    (conj_tac >>
     (irule lowerDloadSafetyImmutableWriteCoverageTheory.ld_istore_operand_unselected >> conj_tac
      >- (qexists_tac `inst` >> simp[])
      >> qexistsl [`A`,`P`] >> simp[])) >>
  `word_agree_except (op_taint tn value) x y` by
    (irule ld_write_scalar_observation >>
     qexistsl [`A`,`P`,`f`,`inst`] >> simp[]) >>
  `op_taint tn addr = {}` by metis_tac[ld_write2_taint] >>
  `dst = dst'` by
    (irule (cj 1 ld_write_address_observation) >>
     qexistsl [`A`,`P`,`f`,`inst`,`addr`,`tn`] >> simp[]) >>
  gvs[] >>
  `?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = addr` by
    simp[mem_write_ops_def] >>
  `MEM (w2n dst,32) (source_memory_write_ranges inst f.lf_src)` by
    simp[source_memory_write_ranges_def, fixed_source_write_range_def,
         eval_operands_def, mem_write_ops_def] >>
  `0 < (32:num)` by simp[] >>
  `(op_prov f.lf_H ops.iao_ofst = NONE ==> dst = dst) /\
   (!k. op_prov f.lf_H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) dst dst)` by
    simp[] >>
  (Q.SUBGOAL_THEN
    `w2n dst+32 <= lo \/
     (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
       w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz) \/
     dyn_floor C vs <= w2n dst` assume_tac
   >- (drule_all (Q.INST [`n` |-> `32`] (cj 2 ld_access_dyn_cases)) >> metis_tac[])) >>
  `op_taint tn value SUBSET {j | j < 32}` by metis_tac[ld_reachable_op_taint_width] >>
  (Q.SUBGOAL_THEN `EVERY (ld_maps A) (f::fs)` assume_tac >- simp[]) >>
  drule_all ld_istore_effect >> strip_tac >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >> strip_tac >>
  qexistsl [`ss`,`f.lf_H`] >> simp[] >>
  `f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H;
            lf_tv := (step_taint inst f.lf_src ss tn).t_var|> =
   f with <|lf_src := ss; lf_tgt := u;
            lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` by
    simp[ld_frame_component_equality] >> simp[]
QED

Resume ld_focus_residual_data_effect[sha3]:
  `inst.inst_opcode = SHA3` by gvs[MEM] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_x_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  drule_all ld_sha3_operands >> strip_tac >>
  drule_all ld_sha3_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >> strip_tac >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
     source_memory_write_ranges inst f.lf_src = []` by
    simp[is_alloca_op_def, write_effects_def, empty_effects_def, source_memory_write_ranges_def] >>
  `step_inst fuel C inst f.lf_src = OK ss /\ step_inst fuel C' inst f.lf_tgt = OK u` by
    simp[step_inst_non_invoke] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by simp[] >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_dyn_agree_unwritten >> strip_tac >>
  qexistsl [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >> simp[] >>
  rpt strip_tac >>
  drule (SRULE [SUBSET_DEF]
    (Q.INST [`q` |-> `NONE`] lowerDloadSafetyUpdatesTheory.ld_set_prov_range)) >>
  simp[]
QED

Finalise ld_focus_residual_data_effect

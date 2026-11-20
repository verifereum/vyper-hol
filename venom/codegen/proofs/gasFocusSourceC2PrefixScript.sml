Theory gasFocusSourceC2Prefix
Ancestors
  o1PipelineCorrect o1SimplifyCfgStageUpto o1SimplifyCfgStageEventsUpto
  o1PruneFocusUpto o1PruneFocusMemory gasFocusMakeSsaStageEvents
  gasFocusMakeSsaStatic o1MakeSsaPtrUpto o1MakeSsaCutTaint o1MakeSsaCutMemory
  o1ContractLowerDloadSim o1ContractLowerDloadStage
  o1ComposeSupport o1PipelineCompose irSupply o1ContractSimplifyCfg
  o1DretDesugarContract unitShapeDefs o1PassContract list o1ContractMakeSsa
  ptrDiscipline o1SafeUpto finite_map unitTransformDefs lowerDloadDefs
  venomState venomPassSchedule venomWf

Theorem focus_source_pre_walk_prefix[local]:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  o1_initial_state_ok V /\ o1_safe_upto D lo n unit.cu_context V /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  n <= LENGTH (gas_events_blocks f unit.cu_context entryfn
    (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
  o1_ctx_shape pre.cu_context /\
  reachable_fcg_acyclic pre.cu_context (fcg_analyze pre.cu_context) /\
  o1_safe_upto D lo n pre.cu_context V /\
  ?fp fnp. pre.cu_context.ctx_entry = SOME nm /\
    lookup_function nm pre.cu_context.ctx_functions = SOME fnp /\
    fn_entry_label fnp = SOME lbl /\
    n <= LENGTH (gas_events_blocks fp pre.cu_context fnp
      (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    TAKE n (gas_events_blocks fp pre.cu_context fnp
      (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
    TAKE n (gas_events_blocks f unit.cu_context entryfn
      (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `reachable_fcg_acyclic pre.cu_context (fcg_analyze pre.cu_context)` by gvs[] >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  qpat_assum `run_pipeline_stages _ _ _ _ = SOME (pre,t)`
    (strip_assume_tac o MATCH_MP o1_pre_walk_runs) >>
  rename1 `run_mapped_functions _ (CFP_Simple VP_DretDesugar) mid tm = SOME (pre,t)` >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) any_view
     unit.cu_context mid.cu_context /\
   o1_ctx_shape mid.cu_context /\ unit_labels_wf mid /\ ir_supply_inst_ok tm` by
    (qpat_assum `run_mapped_functions _ (CFP_Simple VP_SimplifyCFG) _ _ = _`
       (mp_then (Pat `run_mapped_functions _ _ _ _ = _`) mp_tac mapped_pass_stage) >>
     simp[o1_contract_simplify_cfg_pre_walk]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_DretDesugar) any_view
     mid.cu_context pre.cu_context` by
    (qpat_assum `run_mapped_functions _ (CFP_Simple VP_DretDesugar) _ _ = _`
       (mp_then (Pat `run_mapped_functions _ _ _ _ = _`) mp_tac mapped_pass_stage) >>
     simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace]) >>
  `pre.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn))
      unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[EVERY_MEM, unit_defs_reach_uses_def, o1_ctx_shape_def] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all simplify_cfg_stage_safe_upto >> strip_tac >>
  drule_all simplify_cfg_stage_events_upto >> strip_tac >>
  fs[] >> metis_tac[]
QED

Theorem focus_prune_safe_upto[local]:
  o1_ctx_shape pre.cu_context /\ pre.cu_context.ctx_entry = SOME nm /\
  o1_safe_upto D lo n pre.cu_context V ==>
  o1_safe_upto D lo n
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context V
Proof
  rw[o1_safe_upto_def] >- metis_tac[prune_focus_ptr_upto]
  >- metis_tac[prune_focus_headroom] >>
  metis_tac[prune_focus_cut_memory]
QED

Theorem focus_make_ssa_safe_upto[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  V.vs_vars = FEMPTY /\ ~V.vs_halted /\
  o1_safe_upto D lo n C V /\ callee_first names C.ctx_functions ==>
  o1_safe_upto D lo n C' V /\ callee_first names C'.ctx_functions
Proof
  strip_tac >> fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  drule_all make_ssa_focus_static_rows >> strip_tac >>
  drule make_ssa_stage_functions >> strip_tac >>
  simp[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  rpt conj_tac
  >- fs[fixed_region_reserved_def]
  >- metis_tac[make_ssa_stage_ptr_upto]
  >- metis_tac[make_ssa_stage_taint_upto] >>
  rpt strip_tac
  >- (irule make_ssa_stage_raw_memory_upto >> qexists `C` >> simp[] >> metis_tac[]) >>
  irule make_ssa_stage_dload_offset_upto >> qexists `C` >> simp[] >> metis_tac[]
QED

Theorem focus_source_c2_prefix:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  dead_wf D /\
  o1_safe_upto D lo n unit.cu_context
    (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  n <= LENGTH (gas_events_blocks f unit.cu_context entryfn
    (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
                vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  run_callee_first rpolicy o1_fn_passes
    (fcg_postorder (fcg_analyze pre.cu_context) nm)
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,t') /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) ==>
  o1_safe_upto D lo n (stage 1)
    (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  callee_first (fcg_postorder (fcg_analyze pre.cu_context) nm) (stage 1).ctx_functions /\
  EVERY ssa_form (stage 2).ctx_functions /\
  ?f2 fn2. (stage 2).ctx_entry = SOME nm /\
    lookup_function nm (stage 2).ctx_functions = SOME fn2 /\
    fn_entry_label fn2 = SOME lbl /\
    n <= LENGTH (gas_events_blocks f2 (stage 2) fn2
      (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
                  vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    TAKE n (gas_events_blocks f2 (stage 2) fn2
      (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
                  vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
    TAKE n (gas_events_blocks f unit.cu_context entryfn
      (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
                  vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  qabbrev_tac `V = vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> =
   vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
              vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    simp[Abbr `V`, venom_state_component_equality] >>
  qpat_x_assum `_ with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> = _`
    (SUBST_ALL_TAC o SYM) >>
  `o1_initial_state_ok V /\ V.vs_fmp = V.vs_initial_fmp /\ code_layout_valid V /\
   V.vs_vars = FEMPTY /\ ~V.vs_halted` by
    gvs[Abbr `V`, o1_initial_state_ok_def, code_layout_valid_def] >>
  drule_all focus_source_pre_walk_prefix >> strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) (o1_walk_view rpolicy 0)
     (stage 0) (stage 1) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) (o1_walk_view rpolicy 1)
     (stage 1) (stage 2)` by
    (qpat_assum `!k. k < 9 ==> _` (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
     simp[NoAsms, o1_fn_passes_def, arithmeticTheory.ADD1]) >>
  `o1_ctx_shape (stage 0) /\ o1_ctx_shape (stage 1) /\
   EVERY make_ssa_input_ok (stage 0).ctx_functions` by
    (qpat_assum `!k. k <= 9 ==> _` (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
     simp[NoAsms, o1_fn_row_def, EVERY_MEM]) >>
  `o1_safe_upto D lo n (stage 0) V` by metis_tac[focus_prune_safe_upto] >>
  `callee_first (fcg_postorder (fcg_analyze pre.cu_context) nm)
     (stage 0).ctx_functions` by
    ((simp[o1_walk_callee_first])) >>
  drule_all focus_make_ssa_safe_upto >> strip_tac >> simp[] >>
  conj_tac
  >- (drule_all make_ssa_stage_wf_ssa >> strip_tac >>
      irule lower_dload_stage_ssa_form >> goal_assum (drule_at Any) >>
      fs[EVERY_MEM, wf_ssa_def]) >>
  ` (stage 0).ctx_entry = SOME nm /\
    lookup_function nm (stage 0).ctx_functions = SOME fnp /\
    gas_events_blocks fp (stage 0) fnp
      (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
    gas_events_blocks fp pre.cu_context fnp
      (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by
    (qsuff_tac `fcg_analyze pre.cu_context = fcg_analyze pre.cu_context`
     >- (disch_tac >> drule_all prune_focus_entry_events >> fs[]) >> simp[]) >>
  `n <= LENGTH (gas_events_blocks fp (stage 0) fnp
      (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))` by simp[] >>
  drule_all make_ssa_stage_gas_events_upto >> strip_tac >>
  drule_all lower_dload_stage_events_upto >> strip_tac >>
  rename1 `TAKE n (gas_events_blocks f2 (stage 2) fn2 _) = _` >>
  qexistsl [`f2`, `fn2`] >> simp[]
QED

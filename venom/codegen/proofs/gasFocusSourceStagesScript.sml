Theory gasFocusSourceStages
Ancestors
  gasFocusSourceC2Prefix gasFocusLowerDloadCut gasFocusLoweringBridge
  gasFocusPostFmpEntryEvents gasFocusPostFmpCutLoweredMemory
  o1PipelineCompose o1PipelineCorrect codegenEntrySim contextPlanLayoutProps
  o1PassContract o1SafeUpto unitMemInv venomPassSchedule unitTransformDefs
  venomState venomWf lowerDloadDefs gasEvents
  o1ContractLowerDloadStage lowerDloadPtrStatic lowerDloadSupplyProofs
  ptrDiscipline o1ContractSimplifyCfg contextRawReachable
  list arithmetic

Theorem focus_source_stages_cut:
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
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
  o1_safe_upto D lo (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) unit.cu_context
    (vs0 with <|vs_gas_readings := (gs ++ tail); vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  MAP project (gas_events_blocks f unit.cu_context entryfn ((vs0 with <|vs_gas_readings := (gs ++ tail);
    vs_fmp := fmp; vs_initial_fmp := fmp|>) with <|vs_prev_bb := NONE; vs_current_bb := lbl;
    vs_inst_idx := 0|>)) = markf (gs ++ tail) ++ extra /\
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
  mem_inv (\ctx fn inst u. gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (root_entry
    with vs_gas_readings := gs ++ tail) u ==> lowered_mem_fact cpl.cp_max_static_eom ctx fn inst u)
    (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
  ?fn7 f7.
    (stage 7).ctx_entry = SOME nm /\
    lookup_function nm (stage 7).ctx_functions = SOME fn7 /\ fn_entry_label fn7 = SOME lbl /\
    (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) <= LENGTH (gas_events_blocks f7 (stage 7)
      fn7 (root_entry with vs_gas_readings := gs ++ tail)) /\
    TAKE (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (gas_events_blocks f7 (stage 7) fn7
      (root_entry with vs_gas_readings := gs ++ tail)) =
      TAKE (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (gas_events_blocks f unit.cu_context
        entryfn ((vs0 with <|vs_gas_readings := (gs ++ tail); vs_fmp := fmp; vs_initial_fmp := fmp|>) with
        <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `L = gs ++ tail` >>
  qabbrev_tac `n = MIN (LENGTH (markf L)) (LENGTH L)` >>
  `n <= LENGTH (gas_events_blocks f unit.cu_context entryfn
    (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
                vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))` by
    (qpat_assum `MAP project _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[Abbr `n`, venom_state_component_equality] >> decide_tac) >>
  drule_all_then strip_assume_tac focus_source_c2_prefix >>
  qabbrev_tac `V4 = vs0 with vs_gas_readings := L` >>
  qabbrev_tac `V2 = vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `o1_initial_state_ok V4 /\ V4.vs_fmp = V4.vs_initial_fmp /\ code_layout_valid V4 /\
   V4.vs_initial_fmp = vs0.vs_initial_fmp` by
    (gvs[Abbr `V4`, o1_initial_state_ok_def, code_layout_valid_def]) >>
  `V2 = V4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
   o1_initial_state_ok V2 /\ V2.vs_fmp = V2.vs_initial_fmp /\ code_layout_valid V2` by
    (gvs[Abbr `V2`, Abbr `V4`, o1_initial_state_ok_def, code_layout_valid_def]) >>
  qpat_assum `!k. k < 9 ==> ctx_pass_stage _ _ _ _ _`
    (fn th => map_every (fn k => qspec_then k
      (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def, ADD1]) th)
      [`1`,`2`,`3`,`4`,`5`,`6`]) >>
  `o1_ctx_shape (stage 1) /\ o1_ctx_shape (stage 2) /\ o1_ctx_shape (stage 3) /\
   o1_ctx_shape (stage 4) /\ o1_ctx_shape (stage 5) /\ o1_ctx_shape (stage 6) /\
   EVERY (o1_fn_row 2) (stage 2).ctx_functions /\ EVERY (o1_fn_row 4) (stage 4).ctx_functions /\
   EVERY (o1_fn_row 5) (stage 5).ctx_functions /\ EVERY (o1_fn_row 6) (stage 6).ctx_functions /\
   o1_pre 3 (stage 3) (stage 4)` by simp[o1_pre_def] >>
  drule_all_then strip_assume_tac lower_dload_stage_focus_safety >>
  `mem_inv (\ctx fn inst s. gas_cut n V2 s ==> dload_headroom_ok ctx fn inst s)
     (stage 2) V2` by
    simp[mem_inv_raw_reachable] >>
  `!fn inst s. raw_reachable V2 (stage 2) fn inst s /\ gas_cut n V2 s ==>
     raw_mem_ok (stage 2) fn inst s /\ dload_offset_ok (stage 2) fn inst s` by
    metis_tac[] >>
  `o1_ptr_safe_upto D lo n (stage 2) V2` by
    (qpat_assum `o1_safe_upto D lo n (stage 1) V2`
       (strip_assume_tac o REWRITE_RULE [o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
     `(stage 2).ctx_global_reserved = (stage 1).ctx_global_reserved` by
       fs[ctx_pass_stage_def] >>
     drule_all_then assume_tac lower_dload_stage_fmp_free >>
     `EVERY (\fn. fn.fn_eom = NONE) (stage 2).ctx_functions` by
       (irule lower_dload_stage_every >>
        rpt (goal_assum (drule_at Any)) >> simp[] >> rpt strip_tac >>
        drule lower_dload_function_supply_metadata >> simp[]) >>
     simp[o1_ptr_safe_upto_def, fixed_region_reserved_def] >>
     fs[fixed_region_reserved_def]) >>
  drule_all_then assume_tac lower_dload_stage_callee_first >>
  `EVERY all_reachable (stage 2).ctx_functions /\
   EVERY fn_defs_reach_uses (stage 2).ctx_functions /\
   ctx_inst_ids_distinct (stage 2)` by
    fs[EVERY_MEM, o1_fn_row_def, make_ssa_input_ok_def, o1_ctx_shape_def] >>
  `!j. 3 + j <= LENGTH o1_fn_passes ==>
     max_live_eom (stage (3 + j)) = max_live_eom (stage 3)` by
    (drule (REWRITE_RULE [EVAL ``LENGTH o1_fn_passes``]
       o1_walk_stages_max_live_eom) >> simp[o1_fn_passes_def]) >>
  qpat_x_assum `!j. 3 + j <= _ ==> _`
    (fn th => map_every (fn j => qspec_then j
      (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def]) th) [`1`,`6`]) >>
  `max_live_eom out.po_unit.cu_context = SOME cpl.cp_max_static_eom` by
    (drule generate_context_plan_spill_gap >> simp[]) >>
  `max_live_eom (stage 3) = SOME cpl.cp_max_static_eom /\
   max_live_eom (stage 4) = SOME cpl.cp_max_static_eom` by metis_tac[] >>
  `V4.vs_initial_fmp = n2w cpl.cp_initial_fmp` by fs[codegen_asm_entry_rel_def] >>
  `cpl.cp_max_static_eom <= w2n V4.vs_initial_fmp` by
    (qspecl_then [`out.po_unit.cu_context`, `cpl`, `V4`] mp_tac
       generate_context_plan_eom_room >> simp[]) >>
  qpat_x_assum `V4.vs_initial_fmp = n2w _` kall_tac >>
  `w2n V4.vs_initial_fmp <= w2n fmp` by simp[] >>
  `fmp_variant_room (SOME fmp) (stage 4) V4` by
    gvs[fmp_variant_room_def] >>
  `n <= LENGTH (gas_events_blocks f2 (stage 2) fn2
    (V2 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
   TAKE n (gas_events_blocks f2 (stage 2) fn2
    (V2 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
   TAKE n (gas_events_blocks f unit.cu_context entryfn
    (V2 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))` by
    (simp[Abbr `V2`, venom_state_component_equality] >> gvs[]) >>
  drule_all_then strip_assume_tac focus_lowering_cut_bridge >>
  `EVERY make_ssa_input_ok (stage 4).ctx_functions /\
   EVERY wf_ssa (stage 6).ctx_functions` by fs[EVERY_MEM, o1_fn_row_def] >>
  `EVERY simplify_cfg_fn_ok (stage 5).ctx_functions` by
    (fs[EVERY_MEM, o1_ctx_shape_def, o1_fn_shape_def, o1_fn_row_def] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >> metis_tac[]) >>
  drule_all_then assume_tac post_fmp_stages_cut_lowered_memory >>
  (* The event supplier's numeral-only stage index is inferred as rat. *)
  mp_tac (Q.INST [`stageN` |-> `stage`]
           (Q.INST [`f4` |-> `fuel4`,
                    `stage` |-> `\r. stageN (Num (rat$RATN r))`]
             (SPEC_ALL focus_post_fmp_entry_events))) >>
  simp[ratTheory.RATND_RAT_OF_NUM, integerTheory.NUM_OF_INT, o1_fn_passes_def] >>
  disch_then (qx_choose_then `f7` (qx_choose_then `fn7` strip_assume_tac)) >>
  `root_entry with vs_gas_readings := L =
   V4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    simp[Abbr `V4`, venom_state_component_equality] >>
  conj_tac
  >- (qpat_x_assum `mem_inv _ (stage 7) V4` mp_tac >>
      simp[mem_inv_def, contextCodegenRelTheory.codegen_reachability_package_def,
           gas_cut_def, venom_state_component_equality]) >>
  qexistsl [`fn7`, `f7`] >> simp[]
QED

(* Actual covered pass witness for backwards prefix transport. *)
Theory fmpStageCoverForwardActual
Ancestors
  fmpStageRel fmpStepBridge fmpStepLayout concretizeStageLookup
  fmpLowerProps fmpLowerDefs venomFnScheduleRunner
  venomFnScheduleRunnerProps irSupply o1PassContract venomWf venomInst venomFnInstsProofs list

Theorem fmp_stage_covered_lowering:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  ?ctx sp sp'.
    fmp_lower_function ctx sp fn = SOME (fn',sp') /\
    ir_supply_covers_fn sp fn /\ o1_fn_shape C fn
Proof
  strip_tac >>
  `fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\ o1_fn_shape C fn` by
    (gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def,
         fmp_free_ctx_def, o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
     (o1_walk_view rpolicy 3) C C'` by gvs[fmp_stage_ctx_def] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `ir_supply_covers_fn s fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >> metis_tac[lookup_unique_function_member]) >>
  metis_tac[]
QED

Theorem fmp_stage_target_block_ids_distinct:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  lookup_block lbl fn'.fn_blocks = SOME bb' ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)
Proof
  strip_tac >> drule_all fmp_stage_covered_lowering >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     fn'.fn_blocks))` by
    (irule fmp_lower_function_ids_distinct >>
     goal_assum (drule_at Any) >>
     gvs[o1_fn_shape_def, wf_function_def, fn_inst_ids_distinct_def,
         ir_supply_covers_fn_def, fn_ir_inst_ids_def, block_ir_inst_ids_def,
         EVERY_FLAT, EVERY_MAP]) >>
  irule all_distinct_flat_map_member >>
  qexists `MAP (\bb. bb.bb_instructions) fn'.fn_blocks` >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[lookup_block_def] >> drule FIND_MEM >> strip_tac >>
  simp[MEM_MAP] >> metis_tac[]
QED

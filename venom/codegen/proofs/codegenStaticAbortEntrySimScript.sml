Theory codegenStaticAbortEntrySim
Ancestors
  fnStaticAbortBody fnStaticAbortSpec fnStaticAbortBoundary
  fnEntryStep fnEntryPlan fnEntryParams fnBlockStepHelpers
  codegenEntrySim codegenEntryRel codegenLabelDisciplined contextStaticAbortRel
  fnPlanPlaceFnRegion fcgAnalysisProps fcgDefs relation
  fnSimSpec fnBlockBody fnPlanLineage fnBlockBodySteps fnBlockBodyHelpers unitShapeDefs
  venomExecSemantics venomExecProps venomExecProofs venomWf venomInst
  frameRel contextCodegenRel asmSem stackOpSim stackPlanGen callLayoutDefs list rich_list

val _ = Parse.hide "cp";

Theorem gen_fn_abort_simulations:
  !fuel. gen_fn_sim_abort_at fuel /\ gen_fn_frame_sim_abort_at fuel
Proof
  Induct
  >- simp[gen_fn_sim_abort_at_def, gen_fn_frame_sim_abort_at_def, run_blocks_def]
  >> conj_tac
  >- suspend "entry"
  >> suspend "nonentry"
QED

Resume gen_fn_abort_simulations[entry]:
  fs[] >> rewrite_tac[gen_fn_sim_abort_at_def] >> rpt gen_tac >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cpl` >>
  `codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn` by
    (fs[unit_shape_ok_def, codegen_context_obligations_abort_def,
        codegen_ready_def, EVERY_EL, fn_shape_ok_def] >> metis_tac[]) >>
  drule_all region_fn_plan >> strip_tac >>
  drule_all entry_block_plan >> strip_tac >>
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    (rpt strip_tac >> irule region_subplan_spill_offsets >>
     qrefinel [`_`, `_`, `param_ops`, `body_ops ++ rest_ops`,
                `[SOLabel (HD fn.fn_blocks).bb_label]`, `_`] >>
     qexistsl [`cpl`, `ctx`, `r`] >> simp[APPEND_ASSOC]) >>
  `asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
   asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
     qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
     simp[execute_plan_append, asm_block_at_append]) >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  `r.sr_spill_base <= r.sr_spill_base` by simp[] >>
  drule_all (SRULE [] entry_prefix_frame_sim) >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  `run_blocks (SUC fuel) ctx fn vs =
   block_rest fuel ctx fn (HD fn.fn_blocks) vs_p` by
    (irule entry_step_run_rest >> metis_tac[]) >>
  `fn_reachable fn (HD fn.fn_blocks).bb_label` by
    (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  `lineage_state (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state
      (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx (fcg_analyze ctx) fn.fn_name)
      (cleanup_growth_table ctx (fcg_analyze ctx)) r.sr_spill_base lbl_ctr)
    (HD fn.fn_blocks).bb_label
    (init_cleanup_plan_state
      (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx (fcg_analyze ctx) fn.fn_name)
      (cleanup_growth_table ctx (fcg_analyze ctx)) r.sr_spill_base lbl_ctr)` by
    metis_tac[lineage_state_rules] >>
  `phi_prefix_length (HD fn.fn_blocks).bb_instructions <=
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[entry_step_phi_bound] >>
  `!i j. revert_forward_pair (HD fn.fn_blocks) i j ==>
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= i \/
    j < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[revert_forward_pair_past_params] >>
  `body_result_abort lo o2pc prog cpl ctx fn as.as_memory pc_ret rest as'
     (block_rest fuel ctx fn (HD fn.fn_blocks) vs_p)` by
    (irule block_body_frame_sim_abort >>
     simp[NoAsms, body_inv_abort_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qmatch_asmsub_abbrev_tac `lineage_state _ _ _ _ ps0 _ ps0` >>
     qexistsl [`Inv`, `ps0.ps_cleanup_height`, `i`, `lbl_ctr`, `as.as_pc`,
       `param_ops`, `ps0.ps_cleanup_promised`, `ps1`, `ps_after`, `ps0`,
       `ps_after`, `ps_end`, `ps0`, `ra`, `body_ops`, `rpolicy`, `unit`] >>
     gvs[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- fs[fn_entry_state_rel_def] >>
     conj_tac >- (qexistsl [`[]`, `[]`, `ps_after.ps_stack`] >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  gvs[] >> drule_all body_result_abort_prefix >>
  simp[body_result_abort_def] >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[entry_step_return]
QED

Resume gen_fn_abort_simulations[nonentry]:
  fs[] >> rewrite_tac[gen_fn_frame_sim_abort_at_def] >> rpt gen_tac >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cpl` >>
  `codegen_context_obligations (\c f i s. F) ctx cpl` by
    fs[codegen_context_obligations_abort_def, codegen_context_obligations_def,
       codegen_memory_obligations_def] >>
  qspecl_then [`vs`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- suspend "nonentry_ok"
  >> simp[run_blocks_unfold, run_block_def]
QED

Resume gen_fn_abort_simulations[nonentry_ok]:
  `run_blocks (SUC fuel) ctx fn vs =
   block_rest fuel ctx fn bb
     (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[run_blocks_unfold, run_block_def, block_rest_def] >>
     Cases_on `exec_block fuel ctx bb
       (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  `s'.vs_labels = vs.vs_labels /\ s'.vs_call_ctx = vs.vs_call_ctx /\
   s'.vs_current_bb = vs.vs_current_bb` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!inst. active_inst fn inst
            (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
          Inv ctx fn inst
            (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (rpt strip_tac >>
     qpat_x_assum `fn_entry_inv _ _ _ _` (irule o REWRITE_RULE [fn_entry_inv_def]) >>
     simp[enters_block_def]) >>
  drule lineage_entry_lineage_state >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr)
     bb.bb_label ps_dfs` by
    (qpat_x_assum `bb.bb_label = _` (fn th => REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all block_step_prefix >> strip_tac >>
  `!i j. revert_forward_pair bb i j ==>
         phi_prefix_length bb.bb_instructions <= i \/
         j < phi_prefix_length bb.bb_instructions` by
    metis_tac[revert_forward_pair_past_phis] >>
  `body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest as1
    (block_rest fuel ctx fn bb
      (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (irule block_body_frame_sim_abort >>
     simp[NoAsms, body_inv_abort_def] >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]) >>
  drule_all body_result_abort_prefix >>
  simp[body_result_abort_def]
QED

Finalise gen_fn_abort_simulations

Theorem codegen_entry_asm_sim_abort:
  !fuel rpolicy unit cp prog Inv vs es a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    initial_ctx_rel cp prog unit.cu_context vs es /\
    run_context fuel unit.cu_context vs = Abort a vs'
    ==>
    ?n ast.
      (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n (entry_asm_state vs es) = AsmRevert ast \/
       asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n (entry_asm_state vs es) = AsmFault ast) /\
      ast.as_requests = vs'.vs_requests
Proof
  rpt gen_tac >> strip_tac >>
  `?fe rest. unit.cu_context.ctx_functions = fe :: rest /\
             unit.cu_context.ctx_entry = SOME fe.fn_name`
    by gvs[unit_shape_ok_def, entry_fn_first_def] >>
  `get_params (HD fe.fn_blocks).bb_instructions = []`
    by gvs[unit_shape_ok_def] >>
  `?lbl. fn_entry_label fe = SOME lbl /\ reachability_closed Inv unit.cu_context /\
         fn_entry_inv Inv unit.cu_context fe
           (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)`
    by gvs[codegen_reachability_package_def, lookup_function_def, FIND_thm] >>
  `run_blocks fuel unit.cu_context fe
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) =
     Abort a vs'`
    by gvs[run_context_def, run_function_def, lookup_function_def, FIND_thm] >>
  `0 < LENGTH cp.cp_regions`
    by metis_tac[context_region_leading_label, LENGTH, prim_recTheory.LESS_0, EL] >>
  `?r rs. cp.cp_regions = r :: rs` by (Cases_on `cp.cp_regions` >> gvs[]) >>
  `MEM fe.fn_name (fcg_analyze unit.cu_context).fcg_reachable`
    by (qspecl_then [`unit.cu_context`, `fe.fn_name`, `fe.fn_name`]
          mp_tac fcg_analyze_reachable_complete >>
        simp[fcg_is_reachable_def, fcg_path_def, ctx_fn_names_def] >>
        fs[codegen_context_obligations_abort_def]) >>
  `codegen_context_obligations (\c f i s. F) unit.cu_context cp`
    by fs[codegen_context_obligations_abort_def, codegen_context_obligations_def,
          codegen_memory_obligations_def] >>
  mp_tac (Q.INST [`Inv` |-> `\c f i s. F`] codegen_invoke_targets_retpc) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule initial_ctx_codegen_asm_entry_rel >> strip_tac >>
  `fn_entry_state_rel cp fe
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
     (entry_asm_state vs es) 0w []`
    by (irule codegen_asm_entry_fn_state_rel >> metis_tac[]) >>
  `asm_block_at prog 0 (execute_plan cp.cp_initial_fmp r.sr_plan)`
    by metis_tac[codegen_assembly_first_region] >>
  qspec_then `fuel` (mp_tac o CONJUNCT1) gen_fn_abort_simulations >>
  rewrite_tac[gen_fn_sim_abort_at_def] >>
  disch_then (qspecl_then [`rpolicy`, `unit`, `cp`, `prog`, `unit.cu_context`,
    `SND (compute_label_offsets prog)`, `build_offset_to_pc prog`, `0`, `r`, `fe`,
    `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`,
    `entry_asm_state vs es`, `Inv`, `0w`, `0`, `[]`] mp_tac) >>
  impl_tac
  >- (simp[entry_asm_state_def, fn_has_retpc_def] >>
      fs[initial_ctx_rel_def] >>
      gvs[GSYM fn_has_retpc_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> metis_tac[]
QED

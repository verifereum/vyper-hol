Theory gasFocusPlainFrameInitial
Ancestors
  gasFocusPlainEntry fnFramePrefixDriver fnFramePrefixEntry fnFramePrefixStack
  codegenEntrySim codegenEntryFacts codegenEntryRel codegenRel frameRel asmFrameRel asmSem
  fnEntryParams fnPlanPlaceFnRegion fcgAnalysisProps fcgDefs contextCodegenRel
  unitShapeDefs stackPlanGen frameJointTransition o1PassContract
  venomExecSemantics venomState venomWf venomInst list finite_map words

(* Only the empty stack planner uses the normalized base.  The instruction
   entry planner has the pre-PHI and post-PHI states of the raw joint root. *)
Theorem focus_plain_frame_initial:
  generate_context_plan u.cu_context = SOME cpl /\
  codegen_assembly rpolicy u = SOME prog /\ unit_shape_ok u /\
  codegen_context_obligations (\_ _ _ _. F) u.cu_context cpl /\
  o1_run_state_ok vs0 /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0 /\
  joint_initial vs0 u.cu_context q ==>
  normal_frame_plan rpolicy u cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
               vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0 q
    (entry_asm_state vs0 es0)
Proof
  strip_tac >>
  qabbrev_tac `v = vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
    vs_return_pc_token := 0w; vs_inst_idx := 0|>` >>
  `entry_asm_state v es0 = entry_asm_state vs0 es0` by
    simp[Abbr `v`, entry_asm_state_def] >>
  `codegen_asm_entry_rel cpl prog v (entry_asm_state vs0 es0)` by
    fs[Abbr `v`, codegen_asm_entry_rel_def, shared_state_rel_def,
       venom_asm_terminal_rel_def] >>
  `initial_codegen_state_rel cpl v /\ v.vs_inst_idx = 0` by
    fs[Abbr `v`, initial_codegen_state_rel_def, o1_run_state_ok_def,
       codegen_asm_entry_rel_def] >>
  `initial_ctx_rel_tail [] cpl prog u.cu_context v es0` by
    (irule focus_plain_entry_rel >> simp[] >> simp[Abbr `v`]) >>
  `?root others. u.cu_context.ctx_functions = root::others /\
     u.cu_context.ctx_entry = SOME root.fn_name /\
     get_params (HD root.fn_blocks).bb_instructions = []` by
    gvs[unit_shape_ok_def, entry_fn_first_def] >>
  `codegen_ready_fn root` by
    fs[codegen_context_obligations_def, codegen_ready_def] >>
  `?lbl. fn_entry_label root = SOME lbl` by
    (Cases_on `root.fn_blocks` >>
     fs[codegen_ready_fn_def, wf_function_def, fn_has_entry_def,
        fn_entry_label_def, entry_block_def]) >>
  `frame_stack_plan rpolicy u cpl prog v es0 [] root
    (entry_asm_state vs0 es0) 0w [] (entry_asm_state vs0 es0).as_memory` by
    metis_tac[frame_stack_plan_entry, codegen_asm_entry_fn_state_rel] >>
  `fn_entry_state_rel cpl root
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (entry_asm_state vs0 es0) 0w []` by
    metis_tac[codegen_asm_entry_fn_state_rel] >>
  `0 < LENGTH cpl.cp_regions` by
    metis_tac[context_region_leading_label, LENGTH, prim_recTheory.LESS_0, EL] >>
  `?r rs. cpl.cp_regions = r::rs` by
    (Cases_on `cpl.cp_regions` >> fs[]) >>
  `MEM root.fn_name (fcg_analyze u.cu_context).fcg_reachable` by
    (qspecl_then [`u.cu_context`, `root.fn_name`, `root.fn_name`] mp_tac
       fcg_analyze_reachable_complete >>
     simp[fcg_is_reachable_def, fcg_path_def, ctx_fn_names_def] >>
     fs[codegen_context_obligations_def]) >>
  `asm_block_at prog 0 (execute_plan cpl.cp_initial_fmp r.sr_plan)` by
    metis_tac[codegen_assembly_first_region] >>
  `!l. FLOOKUP vs0.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    fs[codegen_asm_entry_rel_def] >>
  qabbrev_tac `start = vs0 with
    <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `entry_frame_plan rpolicy u cpl prog root start start
    (entry_asm_state vs0 es0) 0w 0 [] (entry_asm_state vs0 es0).as_memory` by
    (qsuff_tac `entry_frame_plan rpolicy u cpl prog root start
       (start with vs_inst_idx := 0) (entry_asm_state vs0 es0) 0w 0 []
       (entry_asm_state vs0 es0).as_memory`
     >- simp[Abbr `start`] >>
     irule entry_frame_plan_start >>
     simp[Abbr `start`, entry_asm_state_def, fn_has_retpc_def] >>
     qexists_tac `0` >> simp[]) >>
  qpat_x_assum `joint_initial _ _ _` mp_tac >>
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  gvs[lookup_function_def, FIND_thm] >>
  `enters_block fn start (start with vs_inst_idx := 0)` by
    metis_tac[entry_prefix_enters] >>
  `s1 = start` by gvs[enters_block_def, Abbr `start`] >>
  simp[normal_frame_plan_def] >>
  qexistsl_tac [`entry_asm_state vs0 es0`, `0w`, `[]`,
    `(entry_asm_state vs0 es0).as_memory`] >>
  simp[] >> disj2_tac >> qexistsl_tac [`start`, `0`] >> simp[]
QED

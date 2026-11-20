Theory gasFocusPlainFrameInitialStatic
Ancestors
  gasFocusPlainEntry fnFramePrefixDriver fnFramePrefixEntry fnFramePrefixStack
  codegenEntrySim codegenEntryFacts codegenEntryRel codegenRel frameRel asmFrameRel asmSem
  fnEntryParams fnPlanPlaceDfsBlock contextCodegenRel unitShapeDefs stackPlanGen
  frameJointTransition unitTransformDefs lowerDloadDefs
  venomExecSemantics venomState venomInst list finite_map words

(* The planner normalizes entry fields, but the joint root is still vs0. *)
Theorem focus_plain_frame_initial_static:
  generate_context_plan u.cu_context = SOME cpl /\
  codegen_assembly rpolicy u = SOME prog /\ unit_shape_ok u /\
  codegen_context_obligations (\_ _ _ _. F) u.cu_context cpl /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
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
    fs[Abbr `v`, initial_codegen_state_rel_def, codegen_asm_entry_rel_def] >>
  `initial_ctx_rel_tail [] cpl prog u.cu_context v es0` by
    (irule focus_plain_entry_rel >> simp[] >> simp[Abbr `v`]) >>
  `?root others. u.cu_context.ctx_functions = root::others /\
     u.cu_context.ctx_entry = SOME root.fn_name /\
     get_params (HD root.fn_blocks).bb_instructions = []` by
    gvs[unit_shape_ok_def, entry_fn_first_def] >>
  qpat_x_assum `joint_initial _ _ _` mp_tac >>
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  gvs[lookup_function_def, FIND_thm] >>
  rename1 `fn_entry_label root = SOME lbl` >>
  qmatch_asmsub_abbrev_tac `enters_block root start s1` >>
  `fn_entry_state_rel cpl root start (entry_asm_state vs0 es0) 0w []` by
    (simp[Abbr `start`] >> irule codegen_asm_entry_fn_state_rel >> metis_tac[]) >>
  `codegen_ready_fn root /\ ctx_wf u.cu_context` by
    fs[codegen_context_obligations_def, codegen_ready_def] >>
  `enters_block root start (start with vs_inst_idx := 0)` by
    metis_tac[entry_prefix_enters] >>
  `s1 = start` by gvs[enters_block_def, Abbr `start`] >>
  simp[normal_frame_plan_def] >>
  qexistsl_tac [`entry_asm_state vs0 es0`, `0w`, `[]`,
    `(entry_asm_state vs0 es0).as_memory`] >>
  conj_tac
  >- metis_tac[frame_stack_plan_entry, codegen_asm_entry_fn_state_rel] >>
  disj2_tac >> qexistsl_tac [`start`, `0`] >>
  `?r rs. cpl.cp_regions = r::rs` by
    (drule generate_context_plan_regions_length >> Cases_on `cpl.cp_regions` >> fs[]) >>
  `MEM root.fn_name (fcg_analyze u.cu_context).fcg_reachable` by
    metis_tac[codegen_entry_reachable] >>
  `asm_block_at prog 0 (execute_plan cpl.cp_initial_fmp r.sr_plan)` by
    metis_tac[codegen_assembly_first_region] >>
  `!l. FLOOKUP vs0.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    fs[codegen_asm_entry_rel_def] >>
  qsuff_tac `entry_frame_plan rpolicy u cpl prog root start
    (start with vs_inst_idx := 0) (entry_asm_state vs0 es0) 0w 0 []
    (entry_asm_state vs0 es0).as_memory`
  >- simp[Abbr `start`] >>
  irule entry_frame_plan_start >>
  simp[Abbr `start`, entry_asm_state_def, fn_has_retpc_def] >>
  qexists_tac `0` >> simp[]
QED

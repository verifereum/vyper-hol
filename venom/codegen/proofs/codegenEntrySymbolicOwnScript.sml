(* Relocated symbolic entry composition, conditional on function simulation. *)
Theory codegenEntrySymbolicOwn
Ancestors
  codegenEntryFacts codegenEntrySim symFnSimSpec codegenSymRel
  codegenAsmStaticWf asmSymBridge asmSymSem fnSimSpec frameRel
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomState
  venomInst fcgDefs fcgAnalysisProps fcgPostorder fnPlanPlaceDfsBlock
  venomExecProps venomRetProps rich_list stackPlanGen fragExec

val _ = Parse.hide "cp";

Theorem codegen_entry_sym_init_own_fields:
  as.as_pc = 0 /\ as.as_stack = [] /\ shared_state_rel vs as /\
  vs.vs_code = own /\ asm_data_env_lo_ok lo prog env own ==>
  asm_sym_rel_own lo prog env own as (sym_init as) /\
  (sym_init as).sym_stack = [] /\ (sym_init as).sym_mem_labels = FEMPTY
Proof
  strip_tac >> conj_tac
  >- (irule asm_sym_rel_own_init >> gvs[shared_state_rel_def]) >>
  simp[sym_init_def]
QED

Theorem codegen_entry_layout_fields:
  !cp rpolicy unit prog fe rest as vs.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit.cu_context.ctx_functions = fe :: rest /\ as.as_pc = 0 ==>
    ?r rs. cp.cp_regions = r :: rs /\
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan)
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_regions_length >>
  Cases_on `cp.cp_regions` >> gvs[] >>
  metis_tac[codegen_assembly_first_region]
QED

Theorem codegen_entry_fn_state_rel_fields:
  !cp vs as fe lbl ra.
    as.as_stack = [] /\ ~vs.vs_halted /\ vs.vs_vars = FEMPTY /\
    vs.vs_params = [] /\ n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    context_memory_rel cp vs.vs_memory as.as_memory /\ shared_state_rel vs as /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl ==>
    fn_entry_state_rel cp fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
      as ra []
Proof
  rpt gen_tac >> strip_tac >>
  gvs[fn_entry_label_def, entry_block_def] >>
  gvs[fn_entry_state_rel_def, fn_has_retpc_def,
      shared_state_rel_def, venom_asm_terminal_rel_def]
QED

Theorem codegen_entry_blocks_sym_sim_own_conditional:
  !allow_own lo own fuel cp rpolicy unit prog Inv vs as fe tail lbl env.
    sym_fn_sim_at_own allow_own fuel /\ code_labels_agree prog lo /\
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    as.as_pc = 0 /\ as.as_stack = [] /\ ~vs.vs_halted /\
    vs.vs_vars = FEMPTY /\ vs.vs_params = [] /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    context_memory_rel cp vs.vs_memory as.as_memory /\ shared_state_rel vs as /\
    unit.cu_context.ctx_functions = fe :: tail /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl /\ reachability_closed Inv unit.cu_context /\
    fn_entry_inv Inv unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    (if allow_own then label_flow_own_ok unit.cu_context else label_flow_ok unit.cu_context) /\
    code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own ==>
    (!vs'. run_blocks fuel unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) = Halt vs' ==>
      ?n as'. asm_steps lo (build_offset_to_pc prog) prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n (sym_init as))) /\
    (!a vs'. run_blocks fuel unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\
        asm_steps lo (build_offset_to_pc prog) prog n as = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps lo (build_offset_to_pc prog) prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n (sym_init as)))
Proof
  rpt gen_tac >> strip_tac >>
  `?r rs. cp.cp_regions = r :: rs /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan)`
    by metis_tac[codegen_entry_layout_fields] >>
  `fn_entry_state_rel cp fe
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) as 0w []`
    by metis_tac[codegen_entry_fn_state_rel_fields] >>
  `MEM fe.fn_name (fcg_analyze unit.cu_context).fcg_reachable`
    by (irule codegen_entry_reachable >>
        gvs[unit_shape_ok_def, entry_fn_first_def, codegen_context_obligations_def]) >>
  mp_tac codegen_invoke_targets_retpc >> (impl_tac >- simp[]) >> strip_tac >>
  `asm_sym_rel_own lo prog env own as (sym_init as) /\
    (sym_init as).sym_stack = [] /\ (sym_init as).sym_mem_labels = FEMPTY`
    by metis_tac[codegen_entry_sym_init_own_fields] >>
  qpat_x_assum `sym_fn_sim_at_own _ _` mp_tac >>
  rewrite_tac[sym_fn_sim_at_own_def] >>
  disch_then (drule_at (Pat `fn_entry_state_rel`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  disch_then (drule_at (Pat `codegen_assembly`)) >>
  simp[fn_has_retpc_def] >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`Inv`, `0`] mp_tac) >>
  (impl_tac >- (gvs[fn_has_retpc_def] >> metis_tac[])) >>
  metis_tac[]
QED

Theorem codegen_entry_terminal_own_conditional:
  !allow_own lo own fuel rpolicy unit cp prog Inv vs as env.
    sym_fn_sim_at_own allow_own fuel /\ code_labels_agree prog lo /\
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    as.as_pc = 0 /\ as.as_stack = [] /\ ~vs.vs_halted /\
    vs.vs_vars = FEMPTY /\ vs.vs_params = [] /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    context_memory_rel cp vs.vs_memory as.as_memory /\ shared_state_rel vs as /\
    (if allow_own then label_flow_own_ok unit.cu_context else label_flow_ok unit.cu_context) /\
    code_end_offset_ok Inv unit.cu_context /\ sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    ((?vs'. run_context fuel unit.cu_context vs = Halt vs') \/
     (?a vs'. run_context fuel unit.cu_context vs = Abort a vs')) ==>
    ?n. sym_terminal (sym_steps_mode allow_own prog env own n (sym_init as))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_entry_selection >> strip_tac >>
  `lookup_function fe.fn_name unit.cu_context.ctx_functions = SOME fe`
    by simp[lookup_function_def, listTheory.FIND_thm] >>
  `run_context fuel unit.cu_context vs = run_blocks fuel unit.cu_context fe
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)`
    by metis_tac[run_context_run_blocks] >>
  `asm_static_wf prog`
    by metis_tac[codegen_context_obligations_def, codegen_asm_static_wf] >>
  drule_all codegen_entry_blocks_sym_sim_own_conditional >>
  strip_tac >> metis_tac[]
QED

(*
 * Step 5 of the asm optimizer proof: the assembly codegen emits is
 * label_disciplined (asmSymSem) from codegen's entry state, the premise
 * the asm finalizer contract and the forward bridge need.
 *
 * The entry is stated over a Venom state vs and an assembly state as
 * (codegen_asm_entry_rel), not over an EVM frame: codegen_entry_asm_sim's
 * initial_ctx_rel ties the frame's code to assemble prog and its oracle
 * lists to vs at once, while the optimized program's run needs prog's
 * code and labels with another frame's oracle lists.  initial_ctx_rel
 * gives codegen_asm_entry_rel for entry_asm_state.
 *
 * The premises are codegen_entry_asm_sim's, the label-flow facts of the
 * unit (no CODESIZE; code_end pointers only copied or read by CODECOPY;
 * their offsets below 2^255; a byte-only data segment; INVOKE targets in
 * the context), every data label of the program in env with its bytes
 * from the code (asm_data_env_ok; asm_data_env gives one), and a run that
 * ends (Halt or Abort).  The symbolic run then ends with it
 * (symFnStep's sym_fn_sims_all), so it never misuses a label at any fuel
 * (sym_run_terminal_never_bad).
 *
 * TOP-LEVEL:
 *   codegen_asm_entry_rel         - the assembly entry state of codegen's
 *                                   program for Venom state vs
 *   initial_ctx_codegen_asm_entry_rel - initial_ctx_rel gives it for
 *                                   entry_asm_state
 *   codegen_entry_asm_sim_state   - codegen_entry_asm_sim from it
 *   codegen_label_disciplined     - the program is label_disciplined from it
 *)
Theory codegenLabelDisciplined
Ancestors
  symFnStep symFnSimSpec codegenAsmStaticWf codegenSymRel codegenEntrySim
  codegenEntryRel asmSymBridge asmSymSem fnSimSpec frameRel
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomState
  venomInst fcgDefs fcgAnalysisProps fcgPostorder fnPlanPlaceDfsBlock
  venomExecProps venomRetProps rich_list stackPlanGen fragExec finalizerContract

val _ = Parse.hide "cp";

(* The assembly state as starts codegen's program prog for the Venom
   state vs at the context's entry: at PC 0 with an empty stack, memory
   and shared state related, and vs a fresh, non-static entry state whose
   labels are prog's offsets. *)
Definition codegen_asm_entry_rel_def:
  codegen_asm_entry_rel cp prog vs as <=>
    as.as_pc = 0 /\ as.as_stack = [] /\
    ~vs.vs_halted /\ ~vs.vs_call_ctx.cc_static /\
    vs.vs_vars = FEMPTY /\ vs.vs_params = [] /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    (!l. FLOOKUP vs.vs_labels l =
         OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    shared_state_rel vs as
End

Theorem codegen_asm_entry_fn_state_rel:
  !cp prog vs as fe lbl ra.
    codegen_asm_entry_rel cp prog vs as /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl ==>
    fn_entry_state_rel cp fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
      as ra []
Proof
  rw[codegen_asm_entry_rel_def] >>
  gvs[fn_entry_label_def, entry_block_def] >>
  gvs[fn_entry_state_rel_def, fn_has_retpc_def,
      shared_state_rel_def, venom_asm_terminal_rel_def]
QED

Theorem codegen_asm_entry_sym_init:
  !cp prog vs as env.
    codegen_asm_entry_rel cp prog vs as /\ asm_data_env_ok prog env vs.vs_code ==>
    asm_sym_rel prog env as (sym_init as) /\
    (sym_init as).sym_stack = [] /\
    (sym_init as).sym_mem_labels = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (irule asm_sym_rel_init >>
    gvs[codegen_asm_entry_rel_def, shared_state_rel_def]) >>
  gvs[codegen_asm_entry_rel_def, sym_init_def]
QED

Theorem codegen_entry_reachable:
  ctx_wf ctx /\ ctx.ctx_functions = fe :: rest /\ ctx.ctx_entry = SOME fe.fn_name ==>
  MEM fe.fn_name (fcg_analyze ctx).fcg_reachable
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `fe.fn_name`, `fe.fn_name`]
    fcg_analyze_reachable_complete) >>
  simp[fcg_is_reachable_def, fcg_path_def, ctx_fn_names_def]
QED

Theorem codegen_entry_layout:
  !cp rpolicy unit prog fe rest as vs.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit.cu_context.ctx_functions = fe :: rest /\
    codegen_asm_entry_rel cp prog vs as ==>
    ?r rs. cp.cp_regions = r :: rs /\
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan)
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_regions_length >>
  Cases_on `cp.cp_regions` >> gvs[codegen_asm_entry_rel_def] >>
  metis_tac[codegen_assembly_first_region]
QED

Theorem codegen_entry_selection:
  !unit Inv vs.
    unit_shape_ok unit /\ codegen_reachability_package Inv unit.cu_context vs ==>
    ?fe rest lbl.
      unit.cu_context.ctx_functions = fe :: rest /\
      unit.cu_context.ctx_entry = SOME fe.fn_name /\
      get_params (HD fe.fn_blocks).bb_instructions = [] /\
      entry_fn_no_ret fe /\ fn_entry_label fe = SOME lbl /\
      reachability_closed Inv unit.cu_context /\
      fn_entry_inv Inv unit.cu_context fe
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  rw[unit_shape_ok_def, entry_fn_first_def, codegen_reachability_package_def] >>
  gvs[lookup_function_def, listTheory.FIND_thm] >> metis_tac[]
QED

Theorem codegen_entry_no_returns:
  !cp unit Inv fe rest.
    codegen_context_obligations Inv unit.cu_context cp /\
    unit.cu_context.ctx_functions = fe :: rest /\ entry_fn_no_ret fe ==>
    EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts fe)
Proof
  rpt gen_tac >> strip_tac >> irule entry_no_ret_opcodes >>
  gvs[codegen_context_obligations_def, codegen_ready_def]
QED

Theorem codegen_entry_blocks_sim:
  !fuel cp rpolicy unit prog Inv vs as fe tail lbl.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_asm_entry_rel cp prog vs as /\
    unit.cu_context.ctx_functions = fe :: tail /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl /\ reachability_closed Inv unit.cu_context /\
    fn_entry_inv Inv unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) ==>
    (!vs'. run_blocks fuel unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) = Halt vs' ==>
      ?n as'. asm_steps (SND (compute_label_offsets prog))
        (build_offset_to_pc prog) prog n as = AsmHalt as' /\ venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_blocks fuel unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps (SND (compute_label_offsets prog))
        (build_offset_to_pc prog) prog n as = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps (SND (compute_label_offsets prog))
        (build_offset_to_pc prog) prog n as = AsmFault as')) /\ venom_asm_terminal_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >>
  `?r rs. cp.cp_regions = r :: rs /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan)`
    by metis_tac[codegen_entry_layout] >>
  `fn_entry_state_rel cp fe
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) as 0w []`
    by metis_tac[codegen_asm_entry_fn_state_rel] >>
  `MEM fe.fn_name (fcg_analyze unit.cu_context).fcg_reachable`
    by (irule codegen_entry_reachable >>
        gvs[unit_shape_ok_def, entry_fn_first_def, codegen_context_obligations_def]) >>
  mp_tac codegen_invoke_targets_retpc >> (impl_tac >- simp[]) >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `0`, `ctx` |-> `unit.cu_context`,
    `lo` |-> `SND (compute_label_offsets prog)`, `o2pc` |-> `build_offset_to_pc prog`,
    `ra` |-> `0w`, `pc_ret` |-> `0`, `rest` |-> `[]`, `fn` |-> `fe`,
    `vs` |-> `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`]
    (SPEC_ALL venomToAsmPropsTheory.gen_fn_simulation)) >>
  simp[fn_has_retpc_def] >>
  impl_tac >- (gvs[codegen_asm_entry_rel_def, fn_has_retpc_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem codegen_entry_blocks_sym_sim:
  !fuel cp rpolicy unit prog Inv vs as fe tail lbl env.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_asm_entry_rel cp prog vs as /\
    unit.cu_context.ctx_functions = fe :: tail /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl /\ reachability_closed Inv unit.cu_context /\
    fn_entry_inv Inv unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_ok prog env vs.vs_code ==>
    (!vs'. run_blocks fuel unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) = Halt vs' ==>
      ?n as'. asm_steps (SND (compute_label_offsets prog))
        (build_offset_to_pc prog) prog n as = AsmHalt as' /\ venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n (sym_init as))) /\
    (!a vs'. run_blocks fuel unit.cu_context fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps (SND (compute_label_offsets prog))
        (build_offset_to_pc prog) prog n as = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps (SND (compute_label_offsets prog))
        (build_offset_to_pc prog) prog n as = AsmFault as')) /\ venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n (sym_init as)))
Proof
  rpt gen_tac >> strip_tac >>
  `?r rs. cp.cp_regions = r :: rs /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan)`
    by metis_tac[codegen_entry_layout] >>
  `fn_entry_state_rel cp fe
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) as 0w []`
    by metis_tac[codegen_asm_entry_fn_state_rel] >>
  `MEM fe.fn_name (fcg_analyze unit.cu_context).fcg_reachable`
    by (irule codegen_entry_reachable >>
        gvs[unit_shape_ok_def, entry_fn_first_def, codegen_context_obligations_def]) >>
  mp_tac codegen_invoke_targets_retpc >> (impl_tac >- simp[]) >> strip_tac >>
  `asm_sym_rel prog env as (sym_init as) /\
    (sym_init as).sym_stack = [] /\ (sym_init as).sym_mem_labels = FEMPTY`
    by metis_tac[codegen_asm_entry_sym_init] >>
  qspec_then `fuel` mp_tac (cj 3 sym_fn_sims_all) >>
  rewrite_tac[sym_fn_sim_at_def] >>
  disch_then (mp_tac o Q.INST [`i` |-> `0`, `ctx` |-> `unit.cu_context`,
    `lo` |-> `SND (compute_label_offsets prog)`, `o2pc` |-> `build_offset_to_pc prog`,
    `ra` |-> `0w`, `pc_ret` |-> `0`, `rest` |-> `[]`, `fn` |-> `fe`,
    `vs` |-> `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`,
    `ret` |-> `""`, `srest` |-> `[]`, `ss` |-> `sym_init as`] o SPEC_ALL) >>
  simp[fn_has_retpc_def] >>
  impl_tac >- (gvs[codegen_asm_entry_rel_def, fn_has_retpc_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem initial_ctx_codegen_asm_entry_rel:
  !cp prog ctx vs es.
    initial_ctx_rel cp prog ctx vs es ==>
    codegen_asm_entry_rel cp prog vs (entry_asm_state vs es)
Proof
  cheat
QED

Theorem codegen_entry_asm_sim_state:
  !fuel rpolicy unit cp prog Inv vs as.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    codegen_asm_entry_rel cp prog vs as
    ==>
    (!ret vs'. run_context fuel unit.cu_context vs <> IntRet ret vs') /\
    (!vs'. run_context fuel unit.cu_context vs = Halt vs' ==>
       ?n as'. asm_steps (SND (compute_label_offsets prog))
                 (build_offset_to_pc prog) prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_context fuel unit.cu_context vs = Abort a vs' ==>
       ?n as'.
         ((a = Revert_abort /\
           asm_steps (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) prog n as = AsmRevert as') \/
          (a = ExHalt_abort /\
           asm_steps (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) prog n as = AsmFault as')) /\
         venom_asm_terminal_rel vs' as')
Proof
  cheat
QED

Theorem codegen_label_disciplined:
  !fuel rpolicy unit cp prog Inv vs as env.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    codegen_asm_entry_rel cp prog vs as /\
    label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_ok prog env vs.vs_code /\
    ((?vs'. run_context fuel unit.cu_context vs = Halt vs') \/
     (?a vs'. run_context fuel unit.cu_context vs = Abort a vs'))
    ==>
    label_disciplined env prog as
Proof
  cheat
QED

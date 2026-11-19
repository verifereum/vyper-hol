Theory requestCutStaticEntry
Ancestors
  codegenStaticAbortEntrySim
  codegenEntryFacts
  fnStaticAbortBody fnStaticAbortSpec fnStaticAbortBoundary
  fnEntryStep fnEntryPlan fnEntryParams fnBlockStepHelpers
  codegenEntrySim codegenEntryRel codegenLabelDisciplined contextStaticAbortRel
  fnPlanPlaceFnRegion fcgAnalysisProps fcgDefs relation
  fnSimSpec fnBlockBody fnPlanLineage fnBlockBodySteps fnBlockBodyHelpers unitShapeDefs
  venomExecSemantics venomExecProps venomExecProofs venomWf venomInst
  frameRel contextCodegenRel asmSem stackOpSim stackPlanGen callLayoutDefs list rich_list

val _ = Parse.hide "cp";

Theorem codegen_entry_asm_sim_abort_rel:
  !fuel rpolicy unit cp prog Inv vs ast0 a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    codegen_asm_entry_rel cp prog vs ast0 /\
    run_context fuel unit.cu_context vs = Abort a vs'
    ==>
    ?n ast.
      (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n ast0 = AsmRevert ast \/
       asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n ast0 = AsmFault ast) /\
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
  `fn_entry_state_rel cp fe
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
     ast0 0w []`
    by (irule codegen_asm_entry_fn_state_rel >> metis_tac[]) >>
  `asm_block_at prog 0 (execute_plan cp.cp_initial_fmp r.sr_plan)`
    by metis_tac[codegen_assembly_first_region] >>
  qspec_then `fuel` (mp_tac o CONJUNCT1) gen_fn_abort_simulations >>
  rewrite_tac[gen_fn_sim_abort_at_def] >>
  disch_then (qspecl_then [`rpolicy`, `unit`, `cp`, `prog`, `unit.cu_context`,
    `SND (compute_label_offsets prog)`, `build_offset_to_pc prog`, `0`, `r`, `fe`,
    `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`,
    `ast0`, `Inv`, `0w`, `0`, `[]`] mp_tac) >>
  impl_tac
  >- (fs[codegen_asm_entry_rel_def, fn_has_retpc_def] >>
      gvs[GSYM fn_has_retpc_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> metis_tac[]
QED

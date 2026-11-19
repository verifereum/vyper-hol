Theory staticAbortAsmOptCorrect
Ancestors
  codegenStaticAbortAsmOpt staticAbortFrameException asmFinalizerPrefixStatic
  codegenAsmStaticWf codegenEntryRel contextStaticAbortRel asmOptimizer
  codegenLabelDisciplined codegenSymOwnRel fnPlanPlaceRevertPostamble

Theorem codegen_correct_static_abort_asm_opt:
  !fuel rpolicy unit cp prog prog' Inv vs es a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    label_flow_ok unit.cu_context /\
    code_end_offset_ok
      (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      unit.cu_context /\ sym_unit_static_ok unit /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cp prog vs (entry_asm_state vs es) /\
    asm_frame_rel prog' vs.vs_data_section es
      (entry_asm_state vs es with
        as_code := assemble prog' ++ vs.vs_data_section) es /\
    run_context fuel unit.cu_context vs = Abort a vs' ==>
    (?r es'. run_call es = SOME (r,es') /\
      (frame_resource_starved es r es' \/
       ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)) /\
    call_requests es <<= vs'.vs_requests
Proof
  rpt gen_tac >> strip_tac >>
  `codegen_ready unit.cu_context` by fs[codegen_context_obligations_abort_def] >>
  `asm_static_wf prog` by metis_tac[codegen_asm_static_wf] >>
  `asm_opt_finalizer IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  `asm_frame_prog_ok prog'` by metis_tac[finalizer_prefix_static] >>
  `(entry_asm_state vs es).as_code = assemble prog ++ vs.vs_data_section` by
    simp[entry_asm_state_def] >>
  drule_all_then strip_assume_tac
    codegenStaticAbortAsmOptTheory.codegen_entry_asm_sim_abort_asm_opt >>
  metis_tac[staticAbortFrameExceptionTheory.asm_frame_exception_requests]
QED

(* Statement freeze for sign-off. *)
Theorem codegen_correct_static_abort_asm_opt_own:
  !fuel rpolicy unit cp prog prog' Inv vs es a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    label_flow_own_ok unit.cu_context /\
    code_end_offset_ok
      (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      unit.cu_context /\ sym_unit_static_ok unit /\
    vs.vs_code = assemble prog' ++ vs.vs_data_section /\
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cp prog vs
      (entry_asm_state vs es) /\
    asm_frame_rel prog' vs.vs_data_section es
      (entry_asm_state vs es) es /\
    run_context fuel unit.cu_context vs = Abort a vs' ==>
    (?r es'. run_call es = SOME (r,es') /\
      (frame_resource_starved es r es' \/
       ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)) /\
    call_requests es <<= vs'.vs_requests
Proof
  cheat
QED

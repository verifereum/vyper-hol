Theory codegenStaticAbort
Ancestors
  codegenStaticAbortEntrySim
  codegenStaticAbortFrame

(* Static-prefix spill corruption permits an earlier ASSERT revert. The
   source Error branch accepts either EVM exception; its provenance is
   retained by the caller rather than inferred from this coarse outcome. *)
Theorem codegen_correct_static_abort:
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
    (?r es'. run_call es = SOME (r,es') /\
      (frame_resource_starved es r es' \/
       ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)) /\
    call_requests es <<= vs'.vs_requests
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_entry_asm_sim_abort >> strip_tac >>
  metis_tac[codegen_static_abort_frame]
QED

(* ADMISSION: statement only.  Waits for the optimizer's exceptional-exit preservation proof over pending static-abort regions. *)
Theorem codegen_entry_asm_sim_abort_asm_opt:
  !fuel rpolicy unit cp prog prog' Inv vs s a vs'.
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
    s.as_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cp prog vs s /\
    run_context fuel unit.cu_context vs = Abort a vs' ==>
    ?n ast.
      (asm_steps (SND (compute_label_offsets prog'))
         (build_offset_to_pc prog') prog' n
         (s with as_code := assemble prog' ++ vs.vs_data_section) =
           AsmRevert ast \/
       asm_steps (SND (compute_label_offsets prog'))
         (build_offset_to_pc prog') prog' n
         (s with as_code := assemble prog' ++ vs.vs_data_section) =
           AsmFault ast) /\
      ast.as_requests <<= vs'.vs_requests
Proof
  cheat
QED

(* ADMISSION: statement only.  Waits for its proof from asm_frame_run and asm_frame_run_requests. *)
Theorem asm_frame_exception_requests:
  !prog data es s n ast reqs.
    asm_frame_prog_ok prog /\
    asm_frame_rel prog data es s es /\
    (asm_steps (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog n s = AsmRevert ast \/
     asm_steps (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog n s = AsmFault ast) /\
    ast.as_requests <<= reqs ==>
    (?r es'. run_call es = SOME (r,es') /\
      (frame_resource_starved es r es' \/
       ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)) /\
    call_requests es <<= reqs
Proof
  cheat
QED

(* ADMISSION: statement only.  Waits for its proof from codegen_entry_asm_sim_abort_asm_opt and asm_frame_exception_requests. *)
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
  cheat
QED

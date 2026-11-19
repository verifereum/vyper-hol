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

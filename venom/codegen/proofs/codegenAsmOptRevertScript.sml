(* Optimized codegen preserves revert data and executes REVERT, or starves. *)
Theory codegenAsmOptRevert
Ancestors
  codegenAsmOpt codegenCorrectness

Theorem codegen_reverts_asm_opt:
  !fuel rpolicy unit cplan prog prog' Inv vs vf es.
    generate_context_plan unit.cu_context = SOME cplan /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cplan /\
    codegen_reachability_package Inv unit.cu_context vs /\
    label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cplan prog vs (entry_asm_state vs es) /\
    asm_frame_rel prog' vs.vs_data_section es
      (entry_asm_state vs es with
         as_code := assemble prog' ++ vs.vs_data_section) es /\
    run_context fuel unit.cu_context vs = Abort Revert_abort vf
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/
             ((?lgs. frame_outcome es r es' (SOME Reverted)
                       vf.vs_returndata lgs) /\
              frame_inst_raises es Reverted Revert))
Proof
  rpt strip_tac >>
  qspecl_then [`fuel`, `rpolicy`, `unit`, `cplan`, `prog`, `prog'`,
               `Inv`, `vs`, `es`] mp_tac codegen_correct_asm_opt >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl_tac [`r`, `es'`] >>
  gvs[venom_frame_rel_def]
QED

(* Static and data-environment prerequisites for finalized prefixes. *)
Theory asmFinalizerPrefixStatic
Ancestors
  codegenAsmOpt asmOptFinalizerCorrect asmDataEnv asmFrameRel asmSymSem

Theorem finalizer_prefix_static:
  !fin rp p q x.
    fin IN accepted_finalizers /\ fin rp p = SOME q /\ asm_static_wf p ==>
    asm_static_wf q /\
    FILTER is_data_inst q = FILTER is_data_inst p /\
    asm_frame_prog_ok q /\
    asm_data_env p (assemble p ++ x) = asm_data_env q (assemble q ++ x)
Proof
  rpt strip_tac >>
  drule accepted_finalizers_meet_contract >>
  simp[finalizer_correct_def] >>
  disch_then drule >>
  simp[asm_refines_def] >> strip_tac >>
  metis_tac[asm_static_wf_frame_prog_ok, asm_data_env_agree]
QED

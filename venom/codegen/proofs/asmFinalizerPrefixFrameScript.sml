Theory asmFinalizerPrefixFrame
Ancestors
  asmFrameRun

Theorem finalizer_frame_prefix_ready:
  asm_frame_prog_ok p /\ asm_frame_rel_tail [] p data es0 a es /\
  run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t ==>
  ?B. !n b.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
      p n a = AsmOK b ==>
    n <= B /\
    (b.as_pc < LENGTH p /\ EL b.as_pc p = AsmOp "GAS" ==>
      b.as_gas_readings <> [])
Proof
  strip_tac >>
  drule_all asm_frame_prefix_trace_tail >>
  disch_then (qx_choose_then `bound` strip_assume_tac) >>
  qexists_tac `bound` >> rpt strip_tac
  >- (first_x_assum drule >> strip_tac >> decide_tac) >>
  drule_all asm_frame_prefix_gas_available_tail >>
  simp[]
QED

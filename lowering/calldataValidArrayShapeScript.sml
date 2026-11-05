(* Compiler-only phase witnesses for recursive dynamic-array decoding. *)
Theory calldataValidArrayShape
Ancestors
  abiDecoderLoopEmit abiDecoderArraySetupCode abiDecoderArraySetupInputs
  abiDecoderContract abiDecoderLoopSetup abiDecoderExecution abiEncoder
  compileEnv venomInst list arithmetic abiDecodeRanges

Theorem calldata_array_loop_phase_shapes:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD (Lit 0w) di abi_sz mem_sz ip cnt
    loop_st = ((),final_st) ==>
  ?hdr body_lbl exit_lbl st0 ops ready st1.
    hdr = fresh_label_output "dec_dyn_hdr" loop_st.cs_next_label /\
    body_lbl = fresh_label_output "dec_dyn_body" (loop_st.cs_next_label+1) /\
    exit_lbl = fresh_label_output "dec_dyn_exit" (loop_st.cs_next_label+2) /\
    abi_decode_loop_prefix ip src CALLDATALOAD loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
    st0 = abi_decode_loop_prefix_state ip src CALLDATALOAD loop_st /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di abi_sz mem_sz
      st0 = (ops,ready) /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    ready.cs_blocks = st0.cs_blocks /\ ready.cs_current_bb = st0.cs_current_bb /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
      di ready = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),final_st) /\
    final_st = abi_decode_loop_suffix_state ip
      (STRING #"%" (toString st0.cs_next_var)) hdr exit_lbl st1 /\
    MEM <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
        (STRING #"%" (toString loop_st.cs_next_var))
        (STRING #"%" (toString (loop_st.cs_next_var+1)))
        (STRING #"%" (toString (loop_st.cs_next_var+2)))
        (STRING #"%" (toString (loop_st.cs_next_var+3))) body_lbl exit_lbl|>
      final_st.cs_blocks /\
    MEM <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
        (STRING #"%" (toString st1.cs_next_var)) ip hdr|> final_st.cs_blocks /\
    final_st.cs_current_bb = exit_lbl /\ final_st.cs_current_insts = []
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[abi_decode_loop_prefix_shape] >> strip_tac >> gvs[] >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `(abi_decode_loop_prefix_state ip src CALLDATALOAD loop_st).cs_current_insts = []` by
    simp[abi_decode_loop_prefix_state_def] >>
  drule_all abi_decoder_array_child_phi >> strip_tac >>
  qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  qpat_assum `FST ops = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[abi_decode_loop_suffix_shape] >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  gvs[abi_decode_loop_suffix_state_def, abi_decode_loop_prefix_state_def]
QED

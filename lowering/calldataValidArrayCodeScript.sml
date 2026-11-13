(* Containing-function code for arbitrary recursive calldata array loops. *)
Theory calldataValidArrayCode
Ancestors
  calldataValidArrayShape abiDecoderRecursiveLoopLayout abiDecoderLoopCode abiDecoderLoopEmit
  abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderContract
  fragExec emitHelperProps compileEnv venomInst venomExecSemantics
  abiDecodeRanges list rich_list arithmetic

Theorem calldata_array_phase_lookups[local]:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) start = ((hdr,body_lbl,exit_lbl),st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
    (ops,ready) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w) di
    ready = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),final) /\
  fn_has_code start final fn ==>
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts (start.cs_next_id+1) ip src CALLDATALOAD
        (STRING #"%" (toString start.cs_next_var))
        (STRING #"%" (toString (start.cs_next_var+1)))
        (STRING #"%" (toString (start.cs_next_var+2)))
        (STRING #"%" (toString (start.cs_next_var+3))) body_lbl exit_lbl|> /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
        (STRING #"%" (toString st1.cs_next_var)) ip hdr|> /\
  (?body_bb. lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0) /\
  (?exit_bb. lookup_block exit_lbl fn.fn_blocks = SOME exit_bb)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_loop_prefix_facts >> simp_tac std_ss [] >> strip_tac >>
  drule abi_decoder_loop_phase_lookups >> simp_tac std_ss [] >>
  disch_then drule >> disch_then drule >> simp_tac std_ss [] >>
  disch_then drule >> asm_simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  drule abi_decoder_loop_phase_containment >> simp_tac std_ss [] >>
  disch_then drule >> disch_then drule >> simp_tac std_ss [] >>
  disch_then drule >> asm_simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  drule_all abi_decoder_array_body_entry_phi >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  gvs[fn_has_code_def, abiDecoderExecutionTheory.abi_decode_position_header_delta_def,
      abiDecoderExecutionTheory.abi_decode_position_header_zero] >> metis_tac[]
QED

Theorem calldata_array_loop_function_code:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz ip cnt
    loop_st = ((),final_st) /\ fn_has_code loop_st final_st fn ==>
  ?hdr body_lbl exit_lbl st0 ops ready st1 body_bb exit_bb.
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
    st0 = abi_decode_loop_prefix_state ip src CALLDATALOAD (Lit 0w) loop_st /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz
      st0 = (ops,ready) /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    ready.cs_blocks = st0.cs_blocks /\ ready.cs_current_bb = st0.cs_current_bb /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di ready = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),final_st) /\
    final_st.cs_current_bb = exit_lbl /\ final_st.cs_current_insts = [] /\
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions :=
        abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
          (STRING #"%" (toString loop_st.cs_next_var))
          (STRING #"%" (toString (loop_st.cs_next_var+1)))
          (STRING #"%" (toString (loop_st.cs_next_var+2)))
          (STRING #"%" (toString (loop_st.cs_next_var+3))) body_lbl exit_lbl|> /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
          (STRING #"%" (toString st1.cs_next_var)) ip hdr|> /\
    lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    lookup_block exit_lbl fn.fn_blocks = SOME exit_bb
Proof
  strip_tac >> drule calldata_array_loop_phase_shapes >> strip_tac >>
  drule_all calldata_array_phase_lookups >> strip_tac >>
  qexistsl_tac [`hdr`, `body_lbl`, `exit_lbl`, `st0`, `ops`, `ready`, `st1`,
    `body_bb`, `exit_bb`] >> asm_rewrite_tac[]
QED

(* Exit PHIs belong to the surrounding continuation, not the empty open block. *)
Theorem calldata_array_loop_function_cfg:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz ip cnt
    loop_st = ((),final_st) /\ fn_has_code loop_st final_st fn /\
  (!bb. lookup_block final_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?hdr body_lbl exit_lbl st0 ops ready st1 exit_bb.
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz
      st0 = (ops,ready) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di ready = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),final_st) /\
    abi_decode_loop_cfg fn hdr body_lbl exit_lbl (loop_st.cs_next_id+1) ip src CALLDATALOAD
      (STRING #"%" (toString loop_st.cs_next_var))
      (STRING #"%" (toString (loop_st.cs_next_var+1)))
      (STRING #"%" (toString (loop_st.cs_next_var+2)))
      (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
    (!bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all calldata_array_loop_function_code >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_loop_phase_cfg >> simp_tac std_ss [] >>
  disch_then drule >> disch_then drule >> simp_tac std_ss [] >>
  disch_then drule >> asm_simp_tac bool_ss [] >>
  disch_then (qspec_then `fn` mp_tac) >> asm_simp_tac bool_ss [] >> strip_tac >>
  `st0.cs_current_bb = body_lbl` by
    gvs[abi_decode_loop_prefix_state_def, abi_decode_loop_prefix_shape] >>
  qexistsl_tac [`hdr`, `body_lbl`, `exit_lbl`, `st0`, `ops`, `ready`, `st1`, `exit_bb`] >>
  asm_simp_tac bool_ss [] >>
  gvs[abiDecoderExecutionTheory.abi_decode_position_loop_cfg_def,
      abiDecoderExecutionTheory.abi_decode_loop_cfg_def,
      abiDecoderExecutionTheory.abi_decode_position_header_zero] >> metis_tac[]
QED

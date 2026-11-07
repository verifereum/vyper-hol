(* Actual loop compilation supplies distinct prefix and allocation endpoints. *)
Theory calldataArrayCompileBoundary
Ancestors
  calldataValidArrayCode abiDecoderRecursiveLoopLayout abiDecoderLoopCode
  abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderAppend
  abiDecoderCode abiDecoderCounters fragExec emitHelperProps compileEnv
  venomInst venomExecSemantics abiDecoderContract list arithmetic

Theorem calldata_array_compile_boundary:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD (Lit 0w) di asz msz ip cnt
    loop_st = ((),final_st) /\ fn_has_code loop_st final_st fn /\
  (!bb. lookup_block final_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?hdr body_lbl exit_lbl st0 ops ready st1 exit_bb.
    abi_decode_loop_prefix ip src CALLDATALOAD loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di asz msz st0 =
      (ops,ready) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
      di ready = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),final_st) /\
    fn_has_code loop_st st0 fn /\ fn_has_code st0 ready fn /\
    fn_has_code ready st1 fn /\
    loop_st.cs_next_id < st0.cs_next_id /\ st0.cs_next_id < ready.cs_next_id /\
    ready.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id < final_st.cs_next_id /\
    st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
    st0.cs_next_var = loop_st.cs_next_var + 4 /\
    st0.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= st1.cs_next_var /\
    st1.cs_next_var < final_st.cs_next_var /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decode_loop_cfg fn hdr body_lbl exit_lbl (loop_st.cs_next_id+1) ip src CALLDATALOAD
      (STRING #"%" (toString loop_st.cs_next_var))
      (STRING #"%" (toString (loop_st.cs_next_var+1)))
      (STRING #"%" (toString (loop_st.cs_next_var+2)))
      (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
    (!bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
          (STRING #"%" (toString st1.cs_next_var)) ip hdr|> /\
    lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all calldata_array_loop_function_cfg >> strip_tac >>
  qexistsl_tac [`hdr`, `body_lbl`, `exit_lbl`, `st0`, `ops`, `ready`, `st1`, `exit_bb`] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all (SIMP_RULE std_ss [] (Q.INST
    [`labels` |-> `(hdr,body_lbl,exit_lbl)`] abi_decoder_loop_phase_containment)) >> simp_tac bool_ss [] >> strip_tac >>
  drule_all (SIMP_RULE std_ss [] (Q.INST
    [`labels` |-> `(hdr,body_lbl,exit_lbl)`] abi_decoder_loop_phase_lookups)) >>
  simp_tac std_ss [] >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule abi_decoder_loop_prefix_extends >> strip_tac >>
  `cs_extends st1 final_st` by
    (drule abi_decoder_array_setup_head >> strip_tac >>
     qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [] >> strip_tac >>
     drule abi_decoder_loop_suffix_extends >> simp[]) >>
  `fn_has_code loop_st st1 fn` by
    (mp_tac (Q.SPECL [`loop_st`, `st1`, `final_st`, `fn`] fn_has_code_split) >> simp[]) >>
  `fn_has_code loop_st st0 fn` by
    (mp_tac (Q.SPECL [`loop_st`, `st0`, `st1`, `fn`] fn_has_code_split) >> simp[]) >>
  drule abi_decoder_loop_prefix_facts >> simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule_all abi_decoder_to_buf_code >>
  simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

(* Compiler-only boundary for the joint dynamic-array loop.  No execution
   or child correctness premise is used here. *)
Theory bodyFullAbiDecodeLoopLayout
Ancestors
  abiDecoderRecursiveLoopLayout abiDecoderLoopEmit abiDecoderLoopCode
  abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderContract
  abiEncoder compileEnv emitHelper venomInst venomExecSemantics list arithmetic

Theorem abi_decode_dyn_loop_layout:
  compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt start =
    ((),final_st) /\
  abi_decode_source_opcode opc /\ fn_has_code start final_st fn ==>
  ?labels body ops child returned.
    abi_decode_loop_prefix ip src opc base_op start = (labels,body) /\
    abi_decode_array_element_setup ip src dst opc base_op hi ei asz msz body =
      (ops,child) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc base_op hi ei
      child = ((),returned) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels))
      returned = ((),final_st) /\
    body.cs_current_insts = [] /\
    body.cs_current_bb = FST (SND labels) /\
    FST labels <> body.cs_current_bb /\
    FST labels <> SND (SND labels) /\
    body.cs_current_bb <> SND (SND labels) /\
    FST ops = Var (STRING #"%" (toString body.cs_next_var)) /\
    final_st.cs_current_bb = SND (SND labels) /\
    final_st.cs_current_insts = [] /\
    cs_extends start returned /\ cs_extends body returned /\
    fn_has_code body child fn /\ fn_has_code child returned fn /\
    body.cs_next_var <= child.cs_next_var /\
    child.cs_next_var <= returned.cs_next_var /\
    lookup_block (FST labels) fn.fn_blocks = SOME
      <|bb_label := FST labels; bb_instructions :=
        abi_decode_position_header_insts (start.cs_next_id+1) ip src opc base_op
          start.cs_next_var body.cs_current_bb (SND (SND labels))|> /\
    lookup_block returned.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := returned.cs_current_bb; bb_instructions :=
        returned.cs_current_insts ++
        abi_decode_backedge_insts returned.cs_next_id
          (STRING #"%" (toString body.cs_next_var))
          (STRING #"%" (toString returned.cs_next_var)) ip (FST labels)|>
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  metis_tac[]
QED

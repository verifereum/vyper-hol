(* Derive recursive-loop code premises from the actual four compiler phases. *)
Theory abiDecoderRecursiveLoopLayout
Ancestors
  abiDecoderLoopCode abiDecoderArraySetupCode abiDecoderRecursiveLoopContext
  abiDecoderArrayBody abiDecoderArraySetupInputs abiDecoderAppend abiDecoderPhi
  abiDecoderCode abiDecoderCounters abiDecoderLoopEmit abiDecoderLoopSetup
  abiDecoderExecution abiDecoderContract fragExec compileEnv emitHelper
  emitHelperProps venomInst venomExecSemantics words list rich_list arithmetic

Theorem abi_decoder_loop_prefix_facts:
  abi_decode_loop_prefix ip src opc start = (labels,st) ==>
  st.cs_current_insts = [] /\ st.cs_next_var = start.cs_next_var + 4 /\
  st.cs_next_id = start.cs_next_id + 6 /\ st.cs_current_bb = FST (SND labels) /\
  FST labels <> st.cs_current_bb /\ FST labels <> SND (SND labels) /\
  st.cs_current_bb <> SND (SND labels) /\
  st.cs_blocks =
    <|bb_label := FST labels; bb_instructions :=
      abi_decode_header_insts (start.cs_next_id+1) ip src opc
        (STRING #"%" (toString start.cs_next_var))
        (STRING #"%" (toString (start.cs_next_var+1)))
        (STRING #"%" (toString (start.cs_next_var+2)))
        (STRING #"%" (toString (start.cs_next_var+3))) st.cs_current_bb (SND (SND labels))|> ::
    <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
      [mk_inst start.cs_next_id JMP [Label (FST labels)] []]|> :: start.cs_blocks
Proof
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  gvs[abi_decode_loop_prefix_state_def, fresh_label_output_def]
QED

Theorem abi_decoder_loop_suffix_facts:
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl end_st = ((),final) ==>
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] /\
  final.cs_next_var = end_st.cs_next_var + 1 /\ final.cs_next_id = end_st.cs_next_id + 3 /\
  final.cs_blocks = <|bb_label := end_st.cs_current_bb;
    bb_instructions := end_st.cs_current_insts ++
      abi_decode_backedge_insts end_st.cs_next_id iv
        (STRING #"%" (toString end_st.cs_next_var)) ip hdr|> :: end_st.cs_blocks
Proof
  simp[abi_decode_loop_suffix_shape, abi_decode_loop_suffix_state_def] >> strip_tac >> gvs[]
QED

Theorem abi_decoder_loop_completed_lookups:
  fn_has_code start final func /\ st.cs_blocks = header::entry::start.cs_blocks /\
  end_st.cs_blocks = children ++ st.cs_blocks /\ final.cs_blocks = back::end_st.cs_blocks ==>
  lookup_block header.bb_label func.fn_blocks = SOME header /\
  lookup_block back.bb_label func.fn_blocks = SOME back
Proof
  strip_tac >>
  `final.cs_blocks = (back::children ++ [header;entry]) ++ start.cs_blocks`
    by simp[APPEND_ASSOC] >>
  mp_tac (Q.INST [`st` |-> `start:compile_state`, `end_st` |-> `final:compile_state`,
    `added` |-> `back::children ++ [header;entry]:basic_block list`,
    `bb` |-> `header:basic_block`] abi_decoder_code_completed) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start:compile_state`, `end_st` |-> `final:compile_state`,
    `added` |-> `back::children ++ [header;entry]:basic_block list`,
    `bb` |-> `back:basic_block`] abi_decoder_code_completed) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem abi_decoder_loop_phase_lookups:
  abi_decode_loop_prefix ip src opc start = (labels,st) /\
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func ==>
  lookup_block (FST labels) func.fn_blocks = SOME
    <|bb_label := FST labels; bb_instructions :=
      abi_decode_header_insts (start.cs_next_id+1) ip src opc
        (STRING #"%" (toString start.cs_next_var))
        (STRING #"%" (toString (start.cs_next_var+1)))
        (STRING #"%" (toString (start.cs_next_var+2)))
        (STRING #"%" (toString (start.cs_next_var+3))) st.cs_current_bb (SND (SND labels))|> /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME
    <|bb_label := end_st.cs_current_bb; bb_instructions := end_st.cs_current_insts ++
      abi_decode_backedge_insts end_st.cs_next_id (STRING #"%" (toString st.cs_next_var))
        (STRING #"%" (toString end_st.cs_next_var)) ip (FST labels)|>
Proof
  strip_tac >> drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `?children. end_st.cs_blocks = children ++ st.cs_blocks` by fs[cs_extends_def] >>
  drule_all abi_decoder_loop_completed_lookups >> simp[]
QED

Theorem abi_decoder_loop_phase_cfg:
  abi_decode_loop_prefix ip src opc start = (labels,st) /\
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  abi_decode_loop_cfg func (FST labels) st.cs_current_bb (SND (SND labels)) (start.cs_next_id+1)
    ip src opc (STRING #"%" (toString start.cs_next_var))
      (STRING #"%" (toString (start.cs_next_var+1)))
      (STRING #"%" (toString (start.cs_next_var+2)))
      (STRING #"%" (toString (start.cs_next_var+3))) /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  drule_all abi_decoder_array_body_entry_phi >> strip_tac >>
  drule_all abi_decoder_array_child_phi >> strip_tac >>
  `?exit_bb. lookup_block (SND (SND labels)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `abi_decode_loop_cfg func (FST labels) st.cs_current_bb (SND (SND labels)) (start.cs_next_id+1)
    ip src opc (STRING #"%" (toString start.cs_next_var))
      (STRING #"%" (toString (start.cs_next_var+1)))
      (STRING #"%" (toString (start.cs_next_var+2)))
      (STRING #"%" (toString (start.cs_next_var+3)))` by
    (simp_tac bool_ss [abi_decode_loop_cfg_def] >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >> gvs[] >>
  irule abi_decoder_phi_append >>
  simp[abi_decode_backedge_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_recursive_loop_layout:
  abi_decode_loop_prefix ip src opc start = (labels,st) /\
  abi_decode_array_element_setup ip src dst opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi_op
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ next <= start.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    (FST labels) (SND (SND labels)) (start.cs_next_id+1) start.cs_next_var
    first last lo hi next limit_st site
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_loop_phase_cfg >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  simp_tac bool_ss [abi_decoder_recursive_loop_compiled_def] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >>
  FIRST [decide_tac, qexists_tac
    `<|bb_label := end_st.cs_current_bb; bb_instructions := end_st.cs_current_insts ++
      abi_decode_backedge_insts end_st.cs_next_id (STRING #"%" (toString st.cs_next_var))
        (STRING #"%" (toString end_st.cs_next_var)) ip (FST (labels:string # string # string))|>` >>
    simp[]]
QED

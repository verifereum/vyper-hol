(* Recover entry and completed-block code from actual compiler extensions. *)
Theory abiDecoderLoopCode
Ancestors
  abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderArraySetupCode abiDecoderAppend abiDecoderLoopEmit
  abiDecoderPhi abiDecoderExecution abiDecoderLoopSetup abiDecoderContract
  fragExec compileEnv emitHelperProps emitHelper venomInst venomExecSemantics
  words list rich_list arithmetic

Theorem abi_decoder_code_entry_prefix:
  cs_extends st end_st /\ fn_has_code st end_st func ==>
  ?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX st.cs_current_insts bb.bb_instructions
Proof
  simp_tac bool_ss [cs_extends_def] >> strip_tac >>
  rename1 `end_st.cs_blocks = added ++ st.cs_blocks` >>
  `emitted_blocks st end_st = added` by (irule emitted_blocks_append >> simp[]) >>
  Cases_on `added = []`
  >- (gvs[fn_has_code_def] >> metis_tac[IS_PREFIX_TRANS]) >>
  `MEM (LAST added) added` by simp[MEM_LAST_NOT_NIL] >>
  fs[fn_has_code_def] >> qexists_tac `LAST added` >> simp[] >> metis_tac[]
QED

Theorem abi_decoder_code_completed:
  fn_has_code st end_st func /\ end_st.cs_blocks = added ++ st.cs_blocks /\ MEM bb added ==>
  lookup_block bb.bb_label func.fn_blocks = SOME bb
Proof
  strip_tac >> `emitted_blocks st end_st = added` by
    (irule emitted_blocks_append >> simp[]) >> fs[fn_has_code_def]
QED

Theorem abi_decoder_loop_prefix_extends:
  abi_decode_loop_prefix ip src opc start = (labels,st) ==> cs_extends start st
Proof
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >> gvs[] >>
  simp_tac bool_ss [cs_extends_def, abi_decode_loop_prefix_state_def] >>
  qexists_tac
    `[<|bb_label := fresh_label_output "dec_dyn_hdr" start.cs_next_label;
       bb_instructions := abi_decode_header_insts (start.cs_next_id+1) ip src opc
         (STRING #"%" (toString start.cs_next_var))
         (STRING #"%" (toString (start.cs_next_var+1)))
         (STRING #"%" (toString (start.cs_next_var+2)))
         (STRING #"%" (toString (start.cs_next_var+3)))
         (fresh_label_output "dec_dyn_body" (start.cs_next_label+1))
         (fresh_label_output "dec_dyn_exit" (start.cs_next_label+2))|>;
      <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
        [mk_inst start.cs_next_id JMP [Label (fresh_label_output "dec_dyn_hdr" start.cs_next_label)] []]|>]` >>
  simp[IS_PREFIX_APPEND]
QED

Theorem abi_decoder_loop_suffix_extends:
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl end_st = ((),final) ==> cs_extends end_st final
Proof
  simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >> gvs[] >>
  simp_tac bool_ss [cs_extends_def, abi_decode_loop_suffix_state_def] >>
  qexists_tac `[<|bb_label := end_st.cs_current_bb;
    bb_instructions := end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id iv
      (STRING #"%" (toString end_st.cs_next_var)) ip hdr|>]` >> simp[IS_PREFIX_APPEND]
QED

Theorem abi_decoder_loop_phase_containment:
  abi_decode_loop_prefix ip src opc start = (labels,st) /\
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code start final func ==>
  fn_has_code st end_st func /\ fn_has_code middle end_st func /\
  cs_extends start end_st /\ cs_extends st end_st
Proof
  strip_tac >> drule abi_decoder_array_setup_head >> strip_tac >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule abi_decoder_loop_prefix_extends >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_extends >> strip_tac >>
  `cs_extends st end_st` by (irule cs_extends_trans >> qexists_tac `middle` >> simp[]) >>
  `cs_extends start end_st` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `fn_has_code start end_st func` by (drule_all fn_has_code_split >> simp[]) >>
  `fn_has_code st end_st func` by
    (mp_tac (Q.SPECL [`start`, `st`, `end_st`, `func`] fn_has_code_split) >> simp[]) >>
  mp_tac (Q.SPECL [`st`, `middle`, `end_st`, `func`] fn_has_code_split) >> simp[]
QED

Theorem abi_decoder_array_body_entry_phi:
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  fn_has_code middle end_st func /\ st.cs_current_insts = [] ==>
  ?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule abi_decoder_array_setup_head >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule_all abi_decoder_code_entry_prefix >> strip_tac >>
  qexists_tac `bb` >> gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def]
QED

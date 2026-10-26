(* Pure actual-code contract consumed by encoder loop execution.
   TOP-LEVEL: abi_encoder_array_loop_code and its two actual compiler introductions. *)
Theory abiEncoderArrayLoopCode
Ancestors
  abiEncoderArrayLoopContext abiEncoderArrayLoopLayout abiEncoderArrayScalarCode abiEncoderArrayHeader
  abiEncoderArrayBodyMemory abiEncoderArrayBodyCode abiEncoderArrayDynamicCode abiEncoderArrayPhases
  abiEncoderArrayCode abiEncoderAdmissible abiDecoderIndexInit abiDecoderLoopEmit abiDecoderExecution
  abiDecoderContract fragExec compileEnv emitHelper venomInst venomExecSemantics words list arithmetic

Definition abi_encoder_array_loop_code_def:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels <=>
    fn_has_code body_st body_end func /\
    body_st.cs_next_var = owner_st.cs_next_var+3 /\ body_st.cs_next_id = owner_st.cs_next_id+5 /\
    body_st.cs_current_bb = FST (SND labels) /\ body_st.cs_current_insts = [] /\
    body_st.cs_next_var <= body_end.cs_next_var /\ body_st.cs_next_id <= body_end.cs_next_id /\
    exit_st.cs_next_var = body_end.cs_next_var+1 /\ exit_st.cs_next_id = body_end.cs_next_id+3 /\
    exit_st.cs_current_bb = SND (SND labels) /\ exit_st.cs_current_insts = [] /\
    lookup_block (FST labels) func.fn_blocks = SOME <|bb_label := FST labels; bb_instructions :=
      abi_encode_array_header_insts (owner_st.cs_next_id+1) ip count_op
        (STRING #"%" (toString owner_st.cs_next_var))
        (STRING #"%" (toString (owner_st.cs_next_var+1)))
        (STRING #"%" (toString (owner_st.cs_next_var+2)))
        (FST (SND labels)) (SND (SND labels))|> /\
    lookup_block owner_st.cs_current_bb func.fn_blocks = SOME
      <|bb_label := owner_st.cs_current_bb; bb_instructions := owner_st.cs_current_insts ++
        [mk_inst owner_st.cs_next_id JMP [Label (FST labels)] []]|> /\
    (?bb. lookup_block body_st.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
    (?bb. lookup_block exit_st.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
    lookup_block body_end.cs_current_bb func.fn_blocks = SOME
      <|bb_label := body_end.cs_current_bb; bb_instructions := body_end.cs_current_insts ++
        abi_decode_backedge_insts body_end.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
          (STRING #"%" (toString body_end.cs_next_var)) ip (FST labels)|>
End

Theorem abi_encode_array_static_loop_code:
  abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func ==>
  ?ip owner_st labels body_st idx body_end exit_st.
    abi_decode_index_init start = (ip,owner_st) /\
    abi_encode_array_header ip count_op owner_st = (labels,body_st) /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix ip idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code start owner_st func /\
    fn_has_code exit_st final func /\ abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
    owner_st.cs_next_var = start.cs_next_var+1 /\ owner_st.cs_next_id = start.cs_next_id+2 /\
    body_end.cs_next_var+4 = final.cs_next_var /\ body_end.cs_next_id+6 = final.cs_next_id
Proof
  strip_tac >> drule_all abi_encode_array_static_loop_context >> strip_tac >>
  drule_all abi_encode_array_header_code >> strip_tac >>
  drule abi_encode_array_static_body_index >> disch_tac >>
  qpat_assum `idx = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  drule_all abi_encode_array_suffix_code >> strip_tac >>
  drule_all abi_encode_array_static_entry_phi >>
  disch_then (qx_choose_then `body_bb` strip_assume_tac) >>
  drule_all (cj 1 abi_encode_array_exit_code) >>
  disch_then (qx_choose_then `exit_bb` strip_assume_tac) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule (cj 1 abi_encode_array_exit_shape) >> strip_tac >>
  qexistsl_tac [`ip`, `owner_st`, `labels`, `body_st`,
    `Var (STRING #"%" (toString body_st.cs_next_var))`, `body_end`, `exit_st`] >>
  asm_simp_tac (srw_ss()) [abi_encoder_array_loop_code_def] >> decide_tac
QED

Theorem abi_encode_array_dynamic_loop_code:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func ==>
  ?ptrs owner_st labels body_st idx body_end exit_st.
    abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
    abi_encode_array_header (FST ptrs) count_op owner_st = (labels,body_st) /\
    abi_encode_array_dynamic_body (FST ptrs) (SND ptrs) src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix (FST ptrs) idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_dynamic_exit src (SND ptrs) exit_st = (out,final) /\ fn_has_code start owner_st func /\
    fn_has_code exit_st final func /\
    abi_encoder_array_loop_code func owner_st body_st body_end exit_st (FST ptrs) count_op labels /\
    owner_st.cs_next_var = start.cs_next_var+3 /\ owner_st.cs_next_id = start.cs_next_id+5 /\
    body_end.cs_next_var+4 = final.cs_next_var /\ body_end.cs_next_id+6 = final.cs_next_id
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_loop_context >> strip_tac >>
  drule_all abi_encode_array_header_code >> strip_tac >>
  drule abi_encode_array_dynamic_body_index >> disch_tac >>
  qpat_assum `idx = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  drule_all abi_encode_array_suffix_code >> strip_tac >>
  drule_all abi_encode_array_dynamic_entry_phi >>
  disch_then (qx_choose_then `body_bb` strip_assume_tac) >>
  drule_all (cj 2 abi_encode_array_exit_code) >>
  disch_then (qx_choose_then `exit_bb` strip_assume_tac) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  drule abi_encode_array_dynamic_init_shape >> strip_tac >>
  drule (cj 2 abi_encode_array_exit_shape) >> strip_tac >>
  qexistsl_tac [`ptrs`, `owner_st`, `labels`, `body_st`,
    `Var (STRING #"%" (toString body_st.cs_next_var))`, `body_end`, `exit_st`] >>
  asm_simp_tac (srw_ss()) [abi_encoder_array_loop_code_def] >> decide_tac
QED

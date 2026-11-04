(* Recursive execution over actual source-valid bytes. No execution result or
   canonical re-encoding equality is part of the input observations. *)
Theory abiDecoderValidContract
Ancestors
  abiDecoderCoherence abiDecoderTypedContract abiDecoderPrefixPre abiDecoderCorrect
  abiDecoderEffect abiDecoderAllocation abiDecoderReentry abiDecoderContract abiDecoderLoop
  abiDecodeRanges abiEncoder fragExec compileEnv valueEncoding vyperABI contractABI
  venomState venomExecSemantics words list

Theorem abi_decoder_head_window[simp]:
  abi_member_head_size at <= n ==>
  (is_dynamic at \/ static_length at <= n)
Proof
  Cases_on `is_dynamic at` >> simp[abi_member_head_size_def]
QED

Definition abi_decoder_valid_pre_def:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec (vyper_to_abi_type env ty) bs) v /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      static_length (vyper_to_abi_type env ty) <= LENGTH bs) /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
End

Definition abi_decoder_valid_correct_def:
  abi_decoder_valid_correct ce env sf ty tv <=>
    !dst src opc hi start end_st func ctx first last b cap limit_st initial bs v sb d.
    compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_decoder_valid_pre ce env sf ty tv bs v start src dst opc hi sb d b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?actual. val_in_memory tv v d actual.vs_memory /\
      abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual
End

Theorem abi_decoder_valid_correct_run:
  abi_decoder_valid_correct ce env sf ty tv /\
  compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf ty tv bs v start src dst opc hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_valid_correct _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_valid_correct_def]) >>
  disch_then (qspecl_then [`dst`, `src`, `opc`, `hi`, `start`, `end_st`, `func`, `ctx`,
    `first`, `last`, `b`, `cap`, `limit_st`, `initial`, `bs`, `v`, `sb`, `d`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_pre_prefix:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap s /\
  abi_decoder_reservation st.cs_next_id last b cap s /\
  LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs))) bs =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty)
    (dec (vyper_to_abi_type env ty) bs) v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_recursive_pre_from_prefix >> simp[]
QED

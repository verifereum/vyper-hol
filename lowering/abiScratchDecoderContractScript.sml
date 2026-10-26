(* Actual-source decoder inputs with physical scratch ownership.
   The effect is shared with the encoder and contains no whole-arena write allowance. *)
Theory abiScratchDecoderContract
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiDecoderFootprint abiDecoderAllocation
  abiDecoderCoherence abiDecoderTypedContract abiDecoderFrame abiDecoderReentry
  abiDecoderContract abiDecoderLoop abiDecodeRanges abiEncoder
  compileEnv valueEncoding vyperABI contractABI venomState words list

Definition abi_scratch_decoder_ranges_def:
  abi_scratch_decoder_ranges opc hi src dst sb len d outsz first last b cap s <=>
    abi_decode_source_opcode opc /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    sb + len < dimword (:256) /\ d + outsz < dimword (:256) /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\ sb + len <= h /\ h < dimword (:256)) /\
    abi_footprint_disjoint d outsz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
    (opc = MLOAD ==>
      abi_footprint_disjoint sb len
        ((d,outsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap s))
End

Definition abi_scratch_decoder_input_def:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec (vyper_to_abi_type env ty) bs) v /\
    valid_enc (vyper_to_abi_type env ty) bs /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      static_length (vyper_to_abi_type env ty) <= LENGTH bs) /\
    abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d
      (type_memory_bytes ce ty) first last b cap s /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi
End

Definition abi_scratch_decoder_def:
  abi_scratch_decoder ce env sf ty tv <=>
    !dst src opc hi start end_st func ctx first last b cap limit_st initial bs v sb d.
    compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src dst opc hi sb d
      first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?actual. val_in_memory tv v d actual.vs_memory /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual
End

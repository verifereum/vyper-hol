(* Same-endpoint counted physical decoder contract, shared by recursive constructors. *)
Theory bodyIntCallDecoderCountedContract
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract abiDecoderAllocation
  abiDecoderContract abiEncoder fragGasPath fragExec compileEnv valueEncoding
  venomState venomExecSemantics

Definition intcall_scratch_decoder_counted_def:
  intcall_scratch_decoder_counted ce env sf ty tv <=>
    !dst src opc base_op hi start end_st func ctx first last b cap limit_st initial bs v src_base sb d.
    compile_abi_decode_to_buf dst src opc base_op hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    (base_op = Lit 0w \/ opc = MLOAD) /\
    fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src dst opc base_op hi src_base sb d
      first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor start /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?actual n. val_in_memory tv v d actual.vs_memory /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      gas_path ctx func initial n (OK actual)
End

(* Execute the raw return decoder, preserving its effect and erasing only
   the source-level singleton return wrapper. *)
Theory abiReturnSuccessExecute
Ancestors
  abiReturnSuccessSource abiDecoderValidRecursive abiDecodeUnwrapCase abiBoundaryChecks
  abiDecoderValidContract abiDecoderEffect abiDecoderAllocation abiDecoderReentry
  fragExec exprLowering compileEnv valueEncoding vyperABI venomState words list

Theorem abi_return_valid_decode:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  rtv = (if needs_external_call_wrap ty then TupleTV [tv] else tv) /\
  rv = (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) start = ((),end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf rt rtv (TAKE cap bs) rv start (Lit 0w) dst
    MLOAD base_op hi B 0 d b scratch_cap initial /\
  abi_decoder_budget first last b scratch_cap initial /\
  first <= abi_decoder_entry_floor start /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b scratch_cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`opc` |-> `MLOAD`] abi_decoder_valid_decode |> SIMP_RULE bool_ss []) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >>
  gvs[] >>
  fs[SIMP_RULE bool_ss [] (Q.INST [`unwrap` |-> `T`] abi_decode_output_size)] >>
  Cases_on `needs_external_call_wrap ty` >>
  gvs[val_in_memory_singleton_tuple]
QED

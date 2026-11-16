(* Single contract diagnostic: the scratch operand must predate the header. *)
Theory bodyFullAbiDecodeRuntimeLoop
Ancestors
  abiDecoderReentry abiDecoderExecution emitHelper compileEnv venomInst arithmetic

Theorem abi_decode_counter_liveness_diagnostic[local]:
  ~abi_decoder_operand_live st.cs_next_var
    (Var (STRING #"%" (toString st.cs_next_var))) /\
  FST (emit_op MLOAD [Var (STRING #"%" (toString st.cs_next_var))] st) =
    Var (STRING #"%" (toString st.cs_next_var))
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  metis_tac[LESS_EQ_REFL]
QED

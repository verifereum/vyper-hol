(* Containment and counters for the actual builtin setup and decoder body. *)
Theory abiBuiltinDecodeCode
Ancestors
  abiBuiltinDecodeSetup abiDecoderAppend abiDecoderCounters abiDecoderCode
  abiDecoderContract abiEncoder builtinAbi fragExec compileEnv list arithmetic

Theorem lower_abi_decode_setup_trace:
  lower_abi_decode data info min_size max_size outsz st = (out,final) ==>
  ?ops ready.
    abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (FST (SND ops)) MLOAD (SND (SND ops)) info ready =
      ((),final) /\ out = FST ops
Proof
  simp_tac bool_ss [lower_abi_decode_setup, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready)` >>
  qexistsl_tac [`ops`, `ready`] >> simp[]
QED

Theorem abi_builtin_decode_code:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  compile_abi_decode_to_buf (FST ops) (FST (SND ops)) MLOAD (SND (SND ops)) info ready =
    ((),final) /\ fn_has_code st final func ==>
  fn_has_code st ready func /\ fn_has_code ready final func /\
  ready.cs_blocks = st.cs_blocks /\
  st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= final.cs_next_var /\
  st.cs_next_id <= abi_builtin_decode_output_site st min_size max_size /\
  abi_builtin_decode_output_site st min_size max_size < ready.cs_next_id /\
  ready.cs_next_id <= final.cs_next_id
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends st ready` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `ready`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_to_buf_code >> simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  asm_simp_tac bool_ss [abi_builtin_decode_output_site_def] >> decide_tac
QED

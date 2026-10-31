(* Every actual encoder array phase extends the surrounding CFG. *)
Theory abiEncoderArrayPhaseAppend
Ancestors
  abiEncoderArrayPhases abiEncoderArrayCode abiEncoderChildCode abiEncoderAppend abiDecoderAppend
  abiDecoderDynamicLoopSetup abiDecoderLoopEmit abiDecoderIndexInit fragExec compileEnv
  emitHelper venomInst context list

fun array_phase_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
       cs_appends_abi_alloc_buffer, cs_appends_abi_encode_static_info,
       cj 2 cs_appends_abi_encode_mutual, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- array_phase_append_tac >> rpt gen_tac >> array_phase_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> array_phase_append_tac]) g;

Theorem abi_encode_array_phase_append:
  cs_appends abi_decode_index_init /\
  cs_appends (abi_encode_array_header ip count_op) /\
  cs_appends (abi_encode_array_static_body ip src dst ei asz msz) /\
  cs_appends (abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz) /\
  cs_appends (abi_encode_array_dynamic_init count_op asz) /\
  cs_appends (abi_encode_array_static_exit src asz) /\
  cs_appends (abi_encode_array_dynamic_exit src dyn_ptr) /\
  cs_appends (abi_encode_array_prefix src dst) /\
  cs_appends (abi_encode_array_finish parent_ptr size_op) /\
  cs_appends (abi_decode_loop_suffix ip idx hdr exit_lbl)
Proof
  rewrite_tac [abi_decode_index_init_def, abi_encode_array_header_def,
    abi_encode_array_static_body_def, abi_encode_array_dynamic_body_def,
    abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    abi_encode_child_suffix_def, abi_encode_array_dynamic_init_def,
    abi_encode_array_static_exit_def, abi_encode_array_dynamic_exit_def,
    abi_encode_array_prefix_def, abi_encode_array_finish_def, abi_decode_loop_suffix_def] >>
  rpt conj_tac >> array_phase_append_tac
QED

Theorem abi_encoder_appends_result:
  cs_appends action /\ action st = (out,end_st) ==> cs_extends st end_st
Proof
  simp_tac bool_ss [cs_appends_def] >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `out`, `end_st`] mp_tac) >> asm_simp_tac bool_ss []
QED

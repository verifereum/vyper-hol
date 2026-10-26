(* Typed finite execution follows the actual recursive dynamic-loop compiler. *)
Theory abiDecoderRecursiveDynLoop
Ancestors
  abiDecoderRecursiveLoopLayout abiDecoderRecursiveLoopContext abiDecoderRecursiveLoopFinite
  abiDecoderRecursiveLoopInvariant abiDecoderLoopEmit abiDecoderArraySetupCode
  abiDecoderCorrect abiDecoderEffect abiDecoderExecution abiDecoderLoop
  abiDecoderTypedContract abiDecoderContract
  fragExec compileEnv valueEncoding vyperABI vyperValue venomState words list arithmetic

Theorem abi_decoder_recursive_dyn_loop:
  compile_abi_decode_dyn_loop dst src opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    ip cnt start = ((),final) /\ fn_has_code start final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= site /\ site < start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ next <= start.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi_op ip src dst
    sb d slot b cap next initial /\ abi_decoder_correct ce env sf ty tv /\
  abi_decoder_recursive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) i s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ ~t.vs_halted /\ abi_decode_sim ctx func s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_loop_data_def, abi_decoder_ranges_def,
      Excl "enc_def"] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule_all abi_decoder_recursive_loop_layout >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >> gvs[Excl "enc_def"] >>
  drule_all abi_decoder_recursive_loop_typed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `t` >> simp[]
QED

(* Execute the actual array index allocation while retaining the processed output. *)
Theory abiEncoderArrayIndexPrepare
Ancestors
  abiEncoderZeroCursorPrepare abiEncoderArrayInitCode abiEncoderArrayMemory abiEncoderArrayCursor
  abiEncoderArrayPrefix abiEncoderChildInputs abiEncoderMembersDefs abiDecoderIndexInit
  abiDecoderEffect abiDecoderPrimitiveLoopFrames abiDecoderFrame abiDecoderContract abiDecoderReentry
  fragExec compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_array_memory_mono:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_array_memory ei asz msz active ty avs prepared src dst sb source_cap d output_size b cap j s
Proof
  simp_tac bool_ss [abi_encoder_array_memory_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_buffer_pre_mono >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_index_prepare:
  abi_decode_index_init st = (ip,owner_st) /\ fn_has_code st owner_st func /\
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap j ready /\
    abi_encoder_cursor T ip st.cs_next_id slot first st.cs_next_id owner_st 0 ready /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (ip,owner_st)` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `ip`, `prepared` |-> `owner_st`]
    abi_encoder_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_budget first last b cap ready` by fs[abi_decoder_effect_def] >>
  `owner_st.cs_next_id <= last` by decide_tac >>
  drule_all abi_encoder_cursor_bounds >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_footprint_disjoint d output_size [(slot,32)]` by
    (qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
       (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
     simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac) >>
  `abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j ready` by
    (mp_tac (Q.INST [`dyn` |-> `active:bool`, `fp` |-> `[(slot,32)]`, `lo` |-> `st.cs_next_id`,
      `actual` |-> `ready:venom_state`] abi_encoder_array_memory_scratch) >>
     impl_tac >- asm_simp_tac bool_ss [abi_encoder_array_memory_def] >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= owner_st.cs_next_var` by decide_tac >>
  drule_all abi_encoder_array_memory_mono >> strip_tac >>
  qexistsl_tac [`ready`, `slot`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_INDEX_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array index preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayIndexPrepare");

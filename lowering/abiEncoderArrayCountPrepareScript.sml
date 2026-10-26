(* Actual count copying establishes the empty processed-array prefix. *)
Theory abiEncoderArrayCountPrepare
Ancestors
  abiEncoderArrayCountReach abiEncoderArrayMemory abiEncoderArrayPrefix abiEncoderArrayLayout
  abiEncoderInputLayout abiEncoderInput abiEncoderChildInputs abiEncoderBufferFrame
  abiDecoderCorrectWord abiDecoderArrayLoopInit abiDecoderDynamicLoopSetup abiDecoderEffect
  abiDecoderContract abiDecoderReentry abiDecoderGuards abiDecoderFrameCompose abiDecoderLoop fragExec compileEnv
  valueEncoding valueEncodingProps contractABI venomState words list arithmetic

Theorem abi_encoder_array_buffer_facts:
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap s /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size ==>
  has_type (Array NONE ty) (ListV avs) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ mload sb s = n2w (LENGTH avs) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ 32 <= output_size /\
  (d+output_size <= b \/ b+cap <= d)
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_input_typed >> strip_tac >>
  drule abi_encoder_array_encoding_bound >> strip_tac >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  gvs[mem_word_at_eq_mload, Excl "enc_def"] >> decide_tac
QED

Theorem abi_encoder_array_count_prepare:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_memory ei asz msz active ty avs st' src dst sb source_cap d output_size b cap 0 actual /\
    abi_decoder_operand_live st'.cs_next_var cnt /\ eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_buffer_facts >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_count_live >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  mp_tac (Q.INST [`db` |-> `d:num`] abi_encoder_array_count_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_frame d output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_decoder_scratch_free_effect >> asm_simp_tac (srw_ss()) []) >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap actual` by
    (drule_all abi_encoder_buffer_pre_effect >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size b cap actual` by
    (drule_all abi_encoder_buffer_pre_mono >> asm_simp_tac bool_ss []) >>
  `abi_encoder_array_prefix ty avs 0 d actual.vs_memory` by
    (irule abi_encoder_array_prefix_empty >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_array_memory_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_COUNT_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder count preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayCountPrepare");

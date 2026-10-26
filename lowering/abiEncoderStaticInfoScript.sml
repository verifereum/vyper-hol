(* Execute the real static-array child helper within a larger output buffer. *)
Theory abiEncoderStaticInfo
Ancestors
  abiEncoderAdmissible abiEncoderCorrectLeaves abiEncoderCorrect abiEncoderChildInputs abiEncoderLeafCode
  abiDecoderEffect abiDecoderAllocation abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_static_leaf_correct:
  abi_encoder_static_leaf ei ==> abi_encoder_correct ei
Proof
  rw[abi_encoder_static_leaf_def] >>
  simp[abi_encoder_correct_word, abi_encoder_correct_copy, abi_encoder_correct_empty]
QED

Theorem abi_encoder_buffer_pre_offset:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\
  offset+LENGTH (enc at av) <= output_size ==>
  abi_encoder_pre ei at av st src head sb source_cap (d+offset) b cap initial
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def, abi_encoder_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_static_info_reach:
  abi_encoder_static_leaf ei /\ compile_abi_encode_static_info head src ei st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial actual /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_static_leaf_correct >> disch_tac >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_encoder_buffer_pre_offset >> disch_tac >>
  mp_tac (Q.INST [`start` |-> `st`, `dst` |-> `head`, `d` |-> `d+offset`] abi_encoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`,
       `LENGTH (enc at av)`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_STATIC_INFO_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder static helper execution not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderStaticInfo");

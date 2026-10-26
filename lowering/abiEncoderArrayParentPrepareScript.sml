(* Execute the actual parent allocation and count copy before either array loop. *)
Theory abiEncoderArrayParentPrepare
Ancestors
  abiEncoderArrayInitCode abiEncoderArrayScalarCode abiEncoderArrayCountPrepare abiEncoderZeroCursorPrepare
  abiEncoderComplexPrefix abiEncoderArrayCursor abiEncoderMembersDefs abiEncoderArrayMemory
  abiDecoderArrayLoopInit abiDecoderEffect abiDecoderContract abiDecoderReentry abiDecoderGuards
  abiDecoderLoop fragExec compileEnv emitHelperProps valueEncoding contractABI venomState words list rich_list arithmetic

Theorem abi_encode_array_prefix_context:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func ==>
  ?parent_ptr allocated cnt.
    abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (parent_ptr,allocated) /\
    abi_decode_array_header dst src MLOAD allocated = (cnt,loop_st) /\ ops = (parent_ptr,cnt) /\
    fn_has_code st allocated func /\ fn_has_code allocated loop_st func /\
    allocated.cs_next_var = st.cs_next_var+1 /\ allocated.cs_next_id = st.cs_next_id+2 /\
    loop_st.cs_next_var = st.cs_next_var+2 /\ loop_st.cs_next_id = st.cs_next_id+4
Proof
  strip_tac >> drule abi_encode_array_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `st` |-> `allocated`, `st'` |-> `loop_st`]
    abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  `cs_extends st allocated /\ cs_extends allocated loop_st` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  mp_tac (Q.SPECL [`st`, `allocated`, `loop_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM abi_decode_index_init_complex_prefix]) >>
  pure_rewrite_tac [GSYM abi_decode_index_init_complex_prefix] >>
  qexistsl_tac [`parent_ptr`, `allocated`, `cnt`] >> asm_simp_tac arith_ss []
QED

Theorem abi_encoder_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= hi /\ hi <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_array_memory ei asz msz active ty avs loop_st src dst sb source_cap d output_size b cap 0 actual /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_prefix_context >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= hi /\
   st.cs_next_id < last /\ st.cs_next_id < allocated.cs_next_id /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var /\
   allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `parent_ptr`, `prepared` |-> `allocated`]
    abi_encoder_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial allocated_state` >>
  `fresh_vars_wrt limit_st allocated_state /\ abi_decoder_budget first last b cap allocated_state` by
    fs[abi_decoder_effect_def] >>
  mp_tac (Q.INST [`st` |-> `allocated`, `st'` |-> `loop_st`,
    `initial` |-> `allocated_state:venom_state`, `lo` |-> `allocated.cs_next_id`]
    abi_encoder_array_count_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 actual` by
    (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr`, `site` |-> `st.cs_next_id`,
      `lo` |-> `st.cs_next_id`, `st` |-> `allocated`, `off` |-> `0:num`,
      `owned_lo` |-> `allocated.cs_next_id`, `owned_hi` |-> `hi:num`, `next` |-> `allocated.cs_next_var`,
      `initial` |-> `allocated_state:venom_state`, `sz` |-> `output_size:num`]
      abi_encoder_cursor_effect_protected) >> impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id loop_st 0 actual` by
    (drule_all abi_encoder_cursor_mono >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap allocated_state actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `hi`, `allocated.cs_next_id`, `allocated.cs_next_var`, `output_size`] >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `allocated_state` >> asm_simp_tac bool_ss []) >>
  qpat_assum `loop_st.cs_next_var = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexistsl_tac [`actual`, `slot`] >> asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
  irule abi_decode_sim_trans >> qexists_tac `allocated_state` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_PARENT_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder parent preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayParentPrepare");

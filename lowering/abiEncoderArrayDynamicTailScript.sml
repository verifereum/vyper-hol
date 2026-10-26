(* Execute the real cursor/tail setup, recursive child, and dynamic bookkeeping.
   The selected complete child buffer is supplied by the actual address prefix. *)
Theory abiEncoderArrayDynamicTail
Ancestors
  abiEncoderArrayTailPrepare abiEncoderArrayTail abiEncoderArrayDynamicCode
  abiEncoderDynamicChildCore abiEncoderDynamicChildFinish abiEncoderChildCompose
  abiEncoderChildFrames abiEncoderChildCode abiEncoderChildInputs abiEncoderCorrect abiEncoderCounters abiEncoderResultLive
  abiDecoderEffect abiDecoderAllocation abiDecoderProtectedScratch abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding venomState finite_map
  pred_set words list arithmetic

Theorem abi_encoder_array_dynamic_tail_reach:
  abi_encoder_correct ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
  abi_encoder_buffer_pre ei at av st src data_op sb source_cap d output_size b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\ eval_operand head initial = SOME (n2w (d+ho)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_word_at (d+ho) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand child_len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+ho,32);(d+off,LENGTH (enc at av));(b,cap)] initial actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_shape >> strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >> drule_all abi_encode_array_dynamic_body_child_phi >> disch_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var /\
    st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac abi_encoder_array_tail_prepare >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `abi_decoder_operand_live prepared.cs_next_var head /\
    abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `FLOOKUP ready.vs_allocas site = SOME (slot,32) /\
    eval_operand head ready = SOME (n2w (d+ho))` by fs[abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`start` |-> `prepared`, `end_st` |-> `child_end`, `initial` |-> `ready:venom_state`,
    `dst` |-> `SND (ops:operand # operand)`, `out` |-> `child_len`, `d` |-> `d+off`,
    `offset` |-> `FST (ops:operand # operand)`, `h` |-> `d+ho`] abi_encoder_dynamic_child_core) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `out` |-> `child_len`, `initial` |-> `encoded:venom_state`,
    `offset` |-> `FST (ops:operand # operand)`, `h` |-> `d+ho`,
    `len` |-> `LENGTH (enc at av)`, `bytes` |-> `enc at av`, `hi` |-> `end_st.cs_next_id`]
    abi_encoder_dynamic_child_finish) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `abi_decode_footprint_frame [(d+ho,32);(d+off,LENGTH (enc at av));(b,cap)] initial actual` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `h` |-> `d+ho`, `q` |-> `d+off`,
      `len` |-> `LENGTH (enc at av)`] abi_encoder_dynamic_child_frame) >>
     impl_tac >- fs[abi_decoder_effect_def] >> simp[]) >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `child_end.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `suffix_next` |-> `child_end.cs_next_var`,
    `child_d` |-> `d+off`, `child_sz` |-> `LENGTH (enc at av)`, `sz` |-> `output_size:num`,
    `next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`] abi_encoder_child_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_DYNAMIC_TAIL_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic array tail not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayDynamicTail");

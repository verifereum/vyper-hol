(* Execute the actual dynamic-child wrapper using only the recursive core contract. *)
Theory abiEncoderDynamicChild
Ancestors
  abiEncoderChildContext abiEncoderDynamicChildPrepare abiEncoderDynamicChildCore
  abiEncoderDynamicChildFinish abiEncoderChildCompose abiEncoderChildInputs abiEncoderCorrect
  abiEncoderChildCode abiEncoderChildFrames abiEncoder abiDecoderProtectedScratch abiDecoderEffect abiDecoderAllocation
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec compileEnv valueEncoding venomState finite_map pred_set words list arithmetic

Theorem abi_encoder_dynamic_child_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei T head_offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  head_offset+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    mem_word_at (d+head_offset) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+head_offset,32);(d+off,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
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
  mp_tac abi_encoder_dynamic_child_prepare >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
    abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `FLOOKUP ready.vs_allocas site = SOME (slot,32) /\ eval_operand dyn_ptr ready = SOME (n2w slot)`
    by fs[abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`start` |-> `prepared`, `end_st` |-> `child_end`, `initial` |-> `ready:venom_state`,
    `dst` |-> `SND (SND (ops:operand # operand # operand))`, `out` |-> `child_len`, `d` |-> `d+off`,
    `head` |-> `FST (ops:operand # operand # operand)`, `offset` |-> `FST (SND (ops:operand # operand # operand))`,
    `h` |-> `d+head_offset`] abi_encoder_dynamic_child_core) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> fs[Excl "enc_def"]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `initial` |-> `encoded:venom_state`,
    `head` |-> `FST (ops:operand # operand # operand)`, `offset` |-> `FST (SND (ops:operand # operand # operand))`,
    `h` |-> `d+head_offset`, `len` |-> `LENGTH (enc at av)`, `bytes` |-> `enc at av`,
    `hi` |-> `end_st.cs_next_id`] abi_encoder_dynamic_child_finish) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `abi_decode_footprint_frame [(d+head_offset,32);(d+off,LENGTH (enc at av));(b,cap)] initial actual` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `h` |-> `d+head_offset`, `q` |-> `d+off`,
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
      print ("ABI_ENCODER_DYNAMIC_CHILD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic child not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderDynamicChild");

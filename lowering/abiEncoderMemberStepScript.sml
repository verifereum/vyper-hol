(* Actual static/dynamic child compilation advances the tuple-prefix invariant. *)
Theory abiEncoderMemberStep
Ancestors
  abiEncoderStaticChild abiEncoderDynamicChild abiEncoderTupleStep abiEncoderTuplePrefix
  abiEncoderChildInputs abiEncoderCorrect abiDecoderEffect abiDecoderAllocation abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding valueEncodingProps
  abiCanonicalWindows venomState finite_map words list arithmetic

Theorem abi_encoder_static_member_step:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F heads dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei ty av st src dst sb source_cap d output_size b cap initial /\
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+LENGTH (enc ty av) <= hl /\ hl+tails <= output_size /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d t.vs_memory /\
    eval_operand out t = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decode_footprint_frame [(d+heads,LENGTH (enc ty av));(b,cap)] initial t /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `heads+LENGTH (enc ty av) <= output_size` by decide_tac >>
  mp_tac (Q.INST [`at` |-> `ty:abi_type`, `offset` |-> `heads:num`] abi_encoder_static_child_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac abi_encoder_tuple_static_step >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_dynamic_member_step:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei T heads dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei ty av st src dst sb source_cap d output_size b cap initial /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+32 <= hl /\ off = hl+tails /\ off+LENGTH (enc ty av) <= output_size /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d t.vs_memory /\
    mload slot t = n2w (off+LENGTH (enc ty av)) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decode_footprint_frame [(d+heads,32);(d+off,LENGTH (enc ty av));(b,cap)] initial t /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> `heads+32 <= off` by decide_tac >>
  mp_tac (Q.INST [`at` |-> `ty:abi_type`, `head_offset` |-> `heads:num`] abi_encoder_dynamic_child_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac abi_encoder_tuple_dynamic_step >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [GSYM mem_word_at_eq_mload]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_MEMBER_STEP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder member step not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderMemberStep");

(* Compose actual static-child address setup with the recursive core contract. *)
Theory abiEncoderStaticChild
Ancestors
  abiEncoderAddressReach abiEncoderChildInputs abiEncoderChildCode abiEncoderCorrect abiEncoderChildFrames
  abiEncoderAppend abiEncoderCounters abiEncoder abiDecoderEffect abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec emitHelperProps compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_static_child_context:
  compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?head prepared. emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
    compile_abi_encode_to_buf head src ei prepared = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared end_st func /\
    prepared.cs_next_var = st.cs_next_var+1 /\ prepared.cs_next_id = st.cs_next_id+1 /\
    prepared.cs_blocks = st.cs_blocks /\
    prepared.cs_next_var <= end_st.cs_next_var /\ prepared.cs_next_id <= end_st.cs_next_id /\
    abi_decoder_operand_live prepared.cs_next_var head
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >> drule_all fn_has_code_split >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_static_child_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `dst`, `rhs` |-> `Lit (n2w offset)`,
    `a` |-> `n2w d:bytes32`, `b` |-> `n2w offset:bytes32`, `st'` |-> `prepared`, `out` |-> `head`]
    abi_encoder_binary_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand head ready = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_encoder_pre ei at av prepared src head sb source_cap (d+offset) b cap ready` by
    (mp_tac (Q.INST [`child_st` |-> `prepared`, `child_dst` |-> `head`,
      `actual` |-> `ready:venom_state`] abi_encoder_child_pre_address) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- fs[abi_decoder_address_frame_def] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial ready` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`start` |-> `prepared`, `initial` |-> `ready:venom_state`,
    `dst` |-> `head`, `d` |-> `d+offset`] abi_encoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial actual` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
      `fp` |-> `[(d+offset,LENGTH (enc at av));(b,cap)]`] abi_encoder_frame_after_address) >>
     impl_tac >- fs[abi_decoder_effect_def] >> simp[]) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap ready actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `prepared.cs_next_id`,
       `prepared.cs_next_var`, `LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_STATIC_CHILD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder static child not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderStaticChild");

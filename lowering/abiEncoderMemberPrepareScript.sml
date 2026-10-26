(* The emitted member-source ADD establishes the selected child's complete input. *)
Theory abiEncoderMemberPrepare
Ancestors
  abiEncoderBufferFrame abiEncoderAddressReach abiEncoderChildInputs abiEncoderInput
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec emitHelperProps compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_member_prepare:
  emit_op ADD [src;Lit (n2w (abi_encoder_member_span (TAKE i infos)))] st = (elem_src,prepared) /\
  fn_has_code st prepared func /\
  abi_encoder_buffer_pre (AbiComplex infos) at (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  abi_encoder_tuple_type at ats /\ i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready. abi_encoder_buffer_pre ei (EL i ats) (EL i avs) prepared elem_src dst
      (sb+abi_encoder_member_span (TAKE i infos)) mem_sz d output_size b cap ready /\
    abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
    abi_decoder_operand_live prepared.cs_next_var elem_src /\ fresh_vars_wrt limit_st ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `src`,
    `rhs` |-> `Lit (n2w (abi_encoder_member_span (TAKE i infos)))`, `out` |-> `elem_src`,
    `st'` |-> `prepared`, `a` |-> `n2w sb:bytes32`,
    `b` |-> `n2w (abi_encoder_member_span (TAKE i infos)):bytes32`] abi_encoder_binary_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand elem_src ready = SOME (n2w (sb+abi_encoder_member_span (TAKE i infos)))`
    by fs[word_add_n2w] >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`child_st` |-> `prepared`, `child_src` |-> `elem_src`,
    `actual` |-> `ready:venom_state`] abi_encoder_member_buffer_pre) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_MEMBER_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder member preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderMemberPrepare");

(* Primitive source transport without member invariant or execution owners. *)
Theory abiEncoderChildSourcePhase
Ancestors
  abiEncoderMemberPhaseRaw abiEncoderChildInputs abiEncoderChildCode
  abiEncoderAddressReach emitHelperProps abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_child_static_place_raw_transport:
  emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_encoder_pre ei at av prepared src head sb source_cap (d+offset) b cap ready /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `eval_operand head ready = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
  drule_all abi_encoder_child_pre_address >> simp[]
QED

val _ =
  if List.exists (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
    ["abiEncoderStatic", "abiEncoderDynamic", "abiEncoderMemberSourcePhase", "abiEncoderMembersDefs",
     "abiEncoderMember", "abiScratchStatic", "abiScratchDynamicChild", "abiScratchMembers"]
  then raise Fail "primitive child source phase imports execution owner" else ();

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_child_static_place_raw_transport) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then ()
    else raise Fail "primitive child source phase admission dependency"
  end;

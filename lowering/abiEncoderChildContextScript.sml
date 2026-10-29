(* Extract the three dynamic-child phases with their actual enclosing code. *)
Theory abiEncoderChildContext
Ancestors
  abiEncoderAddressReach abiEncoderChildCode abiEncoderAppend abiEncoderCounters abiEncoderResultLive
  abiDecoderReentry abiDecoderContract fragExec compileEnv emitHelperProps list rich_list arithmetic

Theorem abi_encoder_straight_extends:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' ==>
  cs_extends st st'
Proof
  strip_tac >> irule cs_extends_same_block >>
  gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem abi_encoder_dynamic_child_context:
  compile_abi_encode_child dst src ei T head_offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?ops prepared child_len child_end.
    abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,prepared) /\
    compile_abi_encode_to_buf (SND (SND ops)) src ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (FST ops) dyn_ptr (FST (SND ops)) child_len child_end = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
    prepared.cs_next_var = st.cs_next_var+3 /\ prepared.cs_next_id = st.cs_next_id+3 /\
    prepared.cs_blocks = st.cs_blocks /\
    child_end.cs_next_var+1 = end_st.cs_next_var /\ child_end.cs_next_id+3 = end_st.cs_next_id /\
    end_st.cs_blocks = child_end.cs_blocks /\ end_st.cs_current_bb = child_end.cs_current_bb /\
    prepared.cs_next_var <= child_end.cs_next_var /\ prepared.cs_next_id <= child_end.cs_next_id /\
    abi_decoder_operand_live child_end.cs_next_var child_len
Proof
  strip_tac >> drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule abi_encode_result_live >> strip_tac >>
  `cs_extends st prepared` by (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends child_end end_st` by (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends prepared child_end` by (drule cs_extends_abi_encode >> simp[]) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `child_end` >> simp[]) >>
  mp_tac (Q.SPECL [`st`, `prepared`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `child_end`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`] >> simp[]
QED

Theorem abi_encoder_static_child_structural_context:
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

val _ =
  if List.exists (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
    ["abiEncoderStatic", "abiEncoderDynamic", "abiEncoderMemberSourcePhase", "abiEncoderMembersDefs",
     "abiEncoderMember", "abiScratchStatic", "abiScratchDynamicChild", "abiScratchMembers"]
  then raise Fail "child structural context imports execution owner" else ();

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_static_child_structural_context) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then ()
    else raise Fail "static child structural context admission dependency"
  end;

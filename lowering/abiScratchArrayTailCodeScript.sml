(* Numeric and register resources for the three actual dynamic-child stages.
   TOP-LEVEL: abi_scratch_array_tail_code derives child limits, cursor bounds
   and the real child-exit phi condition from generated code and its budget. *)
Theory abiScratchArrayTailCode
Ancestors
  abiEncoderArrayTail abiEncoderChildCode abiEncoderArrayDynamicCode
  abiEncoderCounters abiEncoderResultLive abiDecoderProtectedScratch
  abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv venomState
  finite_map words list arithmetic

Theorem abi_scratch_array_tail_code:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code child_end end_st func /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_operand_live st.cs_next_var head /\ abi_decoder_operand_live st.cs_next_var dyn_ptr ==>
  prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\
  lo <= prepared.cs_next_id /\ child_end.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_var <= child_end.cs_next_var /\
  site < prepared.cs_next_id /\ site IN abi_decoder_ids first last /\
  site IN abi_decoder_ids lo end_st.cs_next_id /\ slot < dimword (:256) /\
  abi_decoder_operand_live prepared.cs_next_var head /\
  abi_decoder_operand_live child_end.cs_next_var dyn_ptr /\
  abi_decoder_operand_live child_end.cs_next_var child_len /\
  (prepared.cs_blocks = child_end.cs_blocks \/
    !bb. lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule abi_encode_result_live >> strip_tac >>
  drule_all abi_encode_array_dynamic_body_child_phi >> disch_tac >>
  `site IN abi_decoder_ids first last /\ site IN abi_decoder_ids lo end_st.cs_next_id` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by fs[abi_decoder_budget_def] >>
  `slot < dimword (:256)` by decide_tac >>
  `abi_decoder_operand_live prepared.cs_next_var head /\
   abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_TAIL_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array tail code not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayTailCode");

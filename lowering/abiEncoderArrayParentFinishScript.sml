(* Updating the registered parent cursor preserves the completed ABI output and other scratch. *)
Theory abiEncoderArrayParentFinish
Ancestors
  abiEncoderArrayFinishReach abiEncoderChildEffect abiDecoderEffect abiDecoderAllocation
  abiDecoderProtectedScratch abiDecoderArrayInitExec
  abiDecoderPrimitiveLoopFrames abiDecoderFrameCompose abiDecoderFrame abiDecoderContract
  abiDecoderReentry abiDecoderLoop fragExec compileEnv venomState finite_map words list arithmetic pred_set

Theorem abi_encoder_array_parent_finish:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= output_size /\
  (d+output_size <= b \/ b+cap <= d) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\ mload slot actual = n2w len /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`old_word` |-> `0w:bytes32`, `size_word` |-> `n2w len:bytes32`]
    abi_encode_array_finish_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial actual /\
   abi_decode_footprint_frame [(d,output_size);(slot,32)] initial actual` by
    (conj_tac >> irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  `abi_decoder_scratch_frame first last lo hi initial actual` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
      `sz` |-> `output_size:num`] abi_encoder_owned_scratch_frame) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame b cap initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`slot`, `32`] >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,output_size);(b,cap)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `mem_bytes_at d len actual.vs_memory = bytes` by
    (qpat_assum `abi_decode_frame slot 32 initial actual`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `d+len <= slot \/ slot+32 <= d` by decide_tac >>
     qpat_x_assum `!p n. _` (qspecl_then [`d`, `len`] mp_tac) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_PARENT_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder parent finish not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayParentFinish");

(* Update the real registered parent cursor after encoding the array payload.
   TOP-LEVEL: abi_scratch_array_parent_finish preserves all encoded bytes
   using the cursor's physical slot and returns an owned recursive effect. *)
Theory abiScratchArrayParentFinish
Ancestors
  abiScratchEffectCompose abiScratchFootprint abiScratchEncoderContract abiEncoderArrayFinishReach
  abiDecoderAllocation abiDecoderProtectedScratch abiDecoderFrameCompose abiDecoderFrame
  abiDecoderContract abiDecoderReentry abiDecoderLoop compileEnv
  venomState finite_map words list arithmetic

Theorem abi_scratch_array_parent_finish:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= output_size /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\ mload slot actual = n2w len /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[]) >>
  qpat_assum `abi_footprint_disjoint d output_size _`
    (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  mp_tac (Q.INST [`old_word` |-> `0w:bytes32`, `size_word` |-> `n2w len:bytes32`]
    abi_encode_array_finish_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial actual` by fs[abi_decode_frame_footprint] >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`]
    abi_scratch_single_write) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_footprint_disjoint d len [(slot,32)]` by (simp[abi_footprint_disjoint_def] >> decide_tac) >>
  mp_tac (Q.INST [`p` |-> `d:num`, `n` |-> `len:num`, `fp` |-> `[(slot:num,32:num)]`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_decode_footprint_frame_slice) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_PARENT_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch actual parent completion not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayParentFinish");

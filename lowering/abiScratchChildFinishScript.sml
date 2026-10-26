(* Actual post-child stores use physical separation from the parent cursor.
   TOP-LEVEL: abi_scratch_child_finish preserves encoded tail bytes, writes
   the head offset and advances the registered cursor with a two-store frame. *)
Theory abiScratchChildFinish
Ancestors
  abiScratchFootprint abiEncoderChildSuffixReach abiEncoderChildEffect
  abiDecoderAllocation abiDecoderFootprint abiDecoderArrayInitExec abiDecoderFrame abiDecoderProtectedScratch
  abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding
  contractABI venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_child_finish:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\ fn_has_code st st' func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  mem_bytes_at (d+off) len initial.vs_memory = bytes /\
  d <= h /\ h+32 <= d+off /\ off+len <= output_size /\ d+output_size < dimword (:256) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ site IN abi_decoder_ids first last /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) len actual.vs_memory = bytes /\
    mem_word_at h actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+len) /\
    eval_operand out actual = SOME (n2w len) /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_encoder_child_suffix_post out st limit_st h slot off len initial actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by fs[abi_decoder_budget_def] >>
  `h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= d+output_size` by decide_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> asm_simp_tac (srw_ss()) [] >>
     qexists_tac `site` >> simp[]) >>
  qpat_assum `abi_footprint_disjoint d output_size _`
    (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  mp_tac (Q.INST [`p` |-> `slot:num`] abi_encode_child_suffix_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`q` |-> `d+off`, `offset` |-> `off:num`] abi_encoder_child_suffix_output) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `(abi_decoder_budget first last b cap actual <=> abi_decoder_budget first last b cap initial)` by
    (irule abi_decoder_budget_transport >> fs[abi_encoder_child_suffix_post_def]) >>
  `initial.vs_alloca_next <= b+cap` by (drule abi_decoder_budget_frontier >> simp[]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >>
     rw[abi_scratch_evolution_def] >> gvs[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_encoder_child_suffix_post_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_CHILD_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child bookkeeping not kernel closed: " ^ n)
  end) (DB.thms "abiScratchChildFinish");

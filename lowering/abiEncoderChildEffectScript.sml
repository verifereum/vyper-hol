(* Bookkeeping owns its parent cursor site and writes one output head word. *)
Theory abiEncoderChildEffect
Ancestors
  abiEncoderChildSuffixReach abiEncoderChildSuffix abiDecoderEffect abiDecoderProtectedScratch abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderReentry abiDecoderFrame abiDecoderContract
  compileEnv venomState finite_map pred_set words list arithmetic

Theorem abi_encoder_child_suffix_output:
  abi_encoder_child_suffix_post out st limit_st h slot offset len initial actual /\
  mem_bytes_at q len initial.vs_memory = bytes /\
  (q+len <= h \/ h+32 <= q) /\ (q+len <= slot \/ slot+32 <= q) /\
  (h+32 <= slot \/ slot+32 <= h) ==>
  mem_bytes_at q len actual.vs_memory = bytes /\
  mem_word_at h actual.vs_memory = n2w offset /\
  mem_word_at slot actual.vs_memory = n2w (offset+len) /\
  eval_operand out actual = SOME (n2w len)
Proof
  simp_tac bool_ss [abi_encoder_child_suffix_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`p` |-> `slot:num`, `n` |-> `len:num`, `s` |-> `initial:venom_state`,
    `off` |-> `n2w offset:bytes32`, `next` |-> `n2w (offset+len):bytes32`]
    abi_encoder_child_suffix_preserves_tail) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`p` |-> `slot:num`, `s` |-> `initial:venom_state`,
    `off` |-> `n2w offset:bytes32`, `next` |-> `n2w (offset+len):bytes32`]
    abi_encoder_child_suffix_words) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_owned_scratch_frame:
  abi_decoder_budget first last b cap s /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  abi_decode_footprint_frame [(d,sz);(slot,32)] s t /\
  (d+sz <= b \/ b+cap <= d) ==>
  abi_decoder_scratch_frame first last lo hi s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_budget first last b cap t` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  asm_simp_tac bool_ss [abi_decoder_scratch_frame_def] >>
  MAP_EVERY qx_gen_tac [`id`, `p`] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site <> id` by decide_tac >>
  mp_tac (Q.INST [`other` |-> `id:num`, `protected` |-> `p:num`, `outsz` |-> `sz:num`]
    abi_decoder_private_scratch_preserves_slot) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decoder_ids_def] >> simp[]
QED

Theorem abi_encoder_head_scratch_footprint:
  abi_decode_footprint_frame [(h,32);(slot,32)] s t /\
  d <= h /\ h+32 <= d+sz /\ b <= slot /\ slot+32 <= b+cap ==>
  abi_decode_footprint_frame [(d,sz);(b,cap)] s t
Proof
  rw[abi_decode_footprint_frame_def] >> first_x_assum irule >>
  fs[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac
QED

Theorem abi_encoder_child_suffix_effect:
  abi_encoder_child_suffix_post out st limit_st h slot off len initial actual /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  d <= h /\ h+32 <= d+sz /\ (d+sz <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual
Proof
  simp_tac bool_ss [abi_encoder_child_suffix_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `abi_decode_footprint_frame [(d,sz);(slot,32)] initial actual` by
    (irule abi_decoder_output_footprint_widen >> qexistsl_tac [`h`, `32`] >> simp[]) >>
  drule_all abi_encoder_owned_scratch_frame >> strip_tac >>
  drule_all abi_decoder_budget_transport >> strip_tac >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual` by
    (drule_all abi_encoder_head_scratch_footprint >> simp[]) >>
  asm_simp_tac bool_ss [abi_decoder_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CHILD_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder bookkeeping effects not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderChildEffect");

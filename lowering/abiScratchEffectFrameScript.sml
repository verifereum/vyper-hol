(* Enclose a child effect in the physical footprint of its parent interval.
   TOP-LEVEL: abi_scratch_effect_frame exposes a reusable frame for preserving
   complete parent source data and initialized siblings around child execution. *)
Theory abiScratchEffectFrame
Ancestors
  abiScratchEncoderContract abiScratchSubset abiScratchFootprint
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame venomState pred_set list arithmetic

Theorem abi_scratch_effect_frame:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  first <= lo /\ hi <= last ==>
  abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) s t
Proof
  strip_tac >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
  >- (qx_genl_tac [`obs`, `len`] >> strip_tac >>
      qpat_x_assum `abi_footprint_disjoint obs len (_::_)`
        (strip_assume_tac o REWRITE_RULE [abi_scratch_disjoint_cons]) >>
      `abi_footprint_disjoint obs len
        (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
        (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
      `abi_footprint_disjoint obs len
        ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
        simp[abi_scratch_disjoint_cons] >>
      drule_all abi_decode_footprint_frame_slice >> simp[]) >>
  fs[abi_decode_footprint_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_EFFECT_FRAME_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child frame not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEffectFrame");

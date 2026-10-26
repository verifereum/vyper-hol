(* One precise frame for setup, recursive encoding and parent bookkeeping.
   TOP-LEVEL: abi_scratch_dynamic_child_frame keeps the head and encoded tail
   windows separate and charges the cursor store to its actual owned site. *)
Theory abiScratchChildFrame
Ancestors
  abiScratchFrameCompose abiScratchEncoderContract abiScratchFootprint
  abiEncoderChildFrames abiDecoderDynamicLoopSetup abiDecoderFootprint
  abiDecoderFrame venomState finite_map pred_set list arithmetic

Theorem abi_scratch_dynamic_child_frame:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st q len b cap ready encoded /\
  FINITE ids /\ ids SUBSET abi_decoder_ids first last /\
  abi_decoder_ids child_lo child_hi SUBSET ids /\ site IN ids /\
  FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  abi_decode_footprint_frame [(h,32);(slot,32)] encoded actual ==>
  abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap initial) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_scratch_evolution ids b cap ready encoded` by
    (drule_all abi_scratch_evolution_subset >> simp[]) >>
  `abi_decode_footprint_frame
    ([(q,len)] ++ abi_decoder_child_scratch ids b cap ready) ready encoded` by
    (irule abi_scratch_frame_subset_append >> asm_simp_tac bool_ss [] >>
     qexists_tac `abi_decoder_ids child_lo child_hi` >> simp[]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap ready) ready encoded` by
    (simp_tac bool_ss [APPEND] >> irule abi_encoder_frame_extra_window >> gvs[APPEND]) >>
  `MEM (slot,32) (abi_decoder_child_scratch ids b cap encoded)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> simp[]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap encoded) encoded actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(h,32);(slot,32)]` >>
     asm_simp_tac bool_ss [] >> simp[] >> rpt gen_tac >> strip_tac >|
     [qexistsl_tac [`h`, `32`] >> simp[], qexistsl_tac [`slot`, `32`] >> simp[]]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap ready) encoded actual` by
    (drule_all abi_scratch_frame_advance_append >> simp[]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap ready) ready actual` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `encoded` >> simp[]) >>
  `abi_decoder_child_scratch ids b cap ready = abi_decoder_child_scratch ids b cap initial` by
    fs[abi_decoder_address_frame_def, abi_decoder_child_scratch_def] >>
  irule abi_encoder_frame_after_address >> qexistsl_tac [`next`, `ready`] >> gvs[APPEND]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_CHILD_FRAME_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child composed frame not kernel closed: " ^ n)
  end) (DB.thms "abiScratchChildFrame");

(* Turn an actual cursor initializer's observations into its precise effect.
   TOP-LEVEL: abi_scratch_prefix_effect accounts for the sole allocation site
   and the owned frame without excluding the whole numeric scratch arena. *)
Theory abiScratchPrefixEffect
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiEncoderComplexPrefixReach abiEncoderChildFrames
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry compileEnv venomState finite_map words arithmetic

Theorem abi_scratch_prefix_effect:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids site stop) b cap initial) initial actual /\ site < stop ==>
  abi_scratch_effect first last site stop next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids site stop) b cap initial) initial actual` by
    (irule abi_encoder_frame_extra_window >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> rpt gen_tac >> strip_tac >>
  `id <> site` by decide_tac >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_PREFIX_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch initializer effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchPrefixEffect");

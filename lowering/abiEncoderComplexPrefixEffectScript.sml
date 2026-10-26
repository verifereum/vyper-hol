(* The parent cursor's initializer owns its allocation site and preserves other scratch. *)
Theory abiEncoderComplexPrefixEffect
Ancestors
  abiEncoderComplexPrefixReach abiDecoderEffect abiDecoderProtectedScratch
  abiDecoderPrimitiveLoopFrames abiDecoderFrameCompose abiDecoderFrame abiDecoderContract
  abiDecoderAllocation compileEnv venomState words list arithmetic pred_set

Theorem abi_encoder_complex_prefix_effect:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual /\
  first <= site /\ site < hi /\ hi <= last /\ (d+outsz <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last site hi next limit_st d outsz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decode_frame b cap initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`slot`, `32`] >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,outsz);(b,cap)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `abi_decode_footprint_frame [(d,outsz);(slot,32)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `child_first` |-> `site:num`, `child_last` |-> `hi:num`] abi_decoder_child_scratch_preservation) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  `abi_decoder_scratch_frame first last site hi initial actual` by
    (simp_tac bool_ss [abi_decoder_scratch_frame_def] >> conj_tac
     >- (rpt strip_tac >> `id <> site` by decide_tac >> asm_simp_tac bool_ss []) >>
     rpt strip_tac >> `id IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
     qpat_x_assum `!other protected. _` (qspecl_then [`id`, `p`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decoder_effect_def] >> rpt strip_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_COMPLEX_PREFIX_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex prefix effect not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderComplexPrefixEffect");

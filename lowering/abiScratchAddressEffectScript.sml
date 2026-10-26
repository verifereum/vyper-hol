(* Address-only execution is a precise effect for any enclosing output window.
   TOP-LEVEL: abi_scratch_address_effect preserves the allocator budget and
   charges no memory writes, including when execution changes CFG blocks. *)
Theory abiScratchAddressEffect
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderArrayInitExec abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry compileEnv venomState finite_map words arithmetic

Theorem abi_scratch_address_effect:
  abi_decoder_address_frame next initial actual /\ fresh_vars_wrt limit_st actual /\
  abi_decoder_budget first last b cap initial ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `initial.vs_alloca_next <= b+cap` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (simp[abi_scratch_evolution_def] >> rpt strip_tac >> gvs[]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def, abi_decode_footprint_frame_def] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ADDRESS_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch address-only effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchAddressEffect");

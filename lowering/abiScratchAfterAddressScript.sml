(* Reattach an actual address-only prefix to a precise recursive effect.
   TOP-LEVEL: abi_scratch_effect_after_address composes register preservation,
   allocator evolution and the same physical writes from the earlier state. *)
Theory abiScratchAfterAddress
Ancestors
  abiScratchEffect abiScratchEncoderContract abiScratchFootprint abiEncoderChildFrames
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry compileEnv venomState finite_map words arithmetic list

Theorem abi_scratch_effect_after_address:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st child_d child_sz b cap ready actual /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\
  d <= child_d /\ child_d+child_sz <= d+sz ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`child_d`, `child_hi`, `child_lo`, `child_next`, `child_sz`] >> simp[]) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `eval_operand op ready = SOME w` by fs[abi_decoder_address_frame_def] >>
     drule_all abi_scratch_effect_operand >> simp[]) >>
  `(abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual <=>
    abi_scratch_evolution (abi_decoder_ids first last) b cap ready actual)` by
    (irule abi_scratch_evolution_transport >> fs[abi_decoder_address_frame_def]) >>
  `abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap ready =
    abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial` by
    fs[abi_decoder_address_frame_def, abi_decoder_child_scratch_def] >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) ready actual` by
    gvs[abi_scratch_effect_def] >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (irule abi_encoder_frame_after_address >> qexistsl_tac [`next`, `ready`] >> simp[]) >>
  qpat_assum `abi_scratch_effect first last lo hi _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem abi_scratch_frame_after_address:
  abi_decoder_address_frame next initial ready /\
  abi_decode_footprint_frame (fp ++ abi_decoder_child_scratch ids b cap ready) ready actual ==>
  abi_decode_footprint_frame (fp ++ abi_decoder_child_scratch ids b cap initial) initial actual
Proof
  strip_tac >>
  `abi_decoder_child_scratch ids b cap ready = abi_decoder_child_scratch ids b cap initial` by
    fs[abi_decoder_address_frame_def, abi_decoder_child_scratch_def] >>
  irule abi_encoder_frame_after_address >> qexistsl_tac [`next`, `ready`] >> gvs[]
QED

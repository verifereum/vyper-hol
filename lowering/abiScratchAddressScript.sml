Theory abiScratchAddress
Ancestors
  abiScratchFootprint abiDecoderDynamicLoopSetup abiDecoderArrayInitExec abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame venomState pred_set arithmetic abiScratchEncoderContract
  abiDecoderReentry compileEnv finite_map words

(* ===== Scratch Address ===== *)

(* Register-only execution preserves precise scratch ownership and its budget.
   TOP-LEVEL: abi_scratch_address connects the existing address-frame interface
   to scratch evolution and arbitrary observational memory frames. *)

Theorem abi_scratch_address:
  abi_decoder_address_frame next s t /\ abi_decoder_budget first last b cap s ==>
  abi_scratch_evolution ids b cap s t /\ abi_decode_footprint_frame fp s t /\
  abi_decoder_budget first last b cap t /\
  abi_decoder_child_scratch ids b cap t = abi_decoder_child_scratch ids b cap s
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_address_frame _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `s.vs_alloca_next <= b+cap` by
    (drule abi_decoder_budget_frontier >> simp[]) >>
  `abi_scratch_evolution ids b cap s t` by
    (rw[abi_scratch_evolution_def] >> gvs[]) >>
  `(abi_decoder_budget first last b cap t <=> abi_decoder_budget first last b cap s)` by
    (irule abi_decoder_budget_transport >> simp[]) >>
  simp[abi_decode_footprint_frame_def, abi_decoder_child_scratch_def]
QED

(* ===== Effect ===== *)

(* Address-only execution is a precise effect for any enclosing output window.
   TOP-LEVEL: abi_scratch_address_effect preserves the allocator budget and
   charges no memory writes, including when execution changes CFG blocks. *)

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

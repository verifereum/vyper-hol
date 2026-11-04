(* Physical frame composition with a shared list of output windows.
   TOP-LEVEL: subset and frontier-advance rules preserve all observation
   windows while child scratch ownership and allocation state change. *)
Theory abiScratchFrameCompose
Ancestors
  abiScratchSubset abiScratchFootprint abiDecoderFootprint abiDecoderFrame
  venomState pred_set list arithmetic

Theorem abi_scratch_frame_subset_append:
  FINITE ids /\ child_ids SUBSET ids /\
  abi_decode_footprint_frame (fp ++ abi_decoder_child_scratch child_ids b cap s) s t ==>
  abi_decode_footprint_frame (fp ++ abi_decoder_child_scratch ids b cap s) s t
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
  >- (qx_genl_tac [`p`, `n`] >> strip_tac >>
      `abi_footprint_disjoint p n fp /\
       abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s)` by
        fs[abi_footprint_disjoint_append] >>
      `abi_footprint_disjoint p n (abi_decoder_child_scratch child_ids b cap s)` by
        (irule abi_scratch_disjoint_subset >> qexists_tac `ids` >> simp[]) >>
      qpat_x_assum `abi_decode_footprint_frame _ _ _`
        (qspecl_then [`p`, `n`] mp_tac o CONJUNCT1 o
          PURE_REWRITE_RULE [abi_decode_footprint_frame_def]) >>
      simp[abi_footprint_disjoint_append]) >>
  fs[abi_decode_footprint_frame_def]
QED

Theorem abi_scratch_frame_advance_append:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\
  abi_decode_footprint_frame (fp ++ abi_decoder_child_scratch ids b cap t) t u ==>
  abi_decode_footprint_frame (fp ++ abi_decoder_child_scratch ids b cap s) t u
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
  >- (qx_genl_tac [`p`, `n`] >> strip_tac >>
      `abi_footprint_disjoint p n fp /\
       abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s)` by
        fs[abi_footprint_disjoint_append] >>
      `abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap t)` by
        (drule_all abi_scratch_disjoint_advance >> simp[]) >>
      qpat_x_assum `abi_decode_footprint_frame _ _ _`
        (qspecl_then [`p`, `n`] mp_tac o CONJUNCT1 o
          PURE_REWRITE_RULE [abi_decode_footprint_frame_def]) >>
      simp[abi_footprint_disjoint_append]) >>
  fs[abi_decode_footprint_frame_def]
QED

(* Numeric-envelope compatibility at the shared encoder boundary. *)
Theory abiEncoderEnvelopeAdapter
Ancestors
  abiEncoderSharedContract abiEncoderCorrect abiScratchEffect abiDecoderEffect
  abiDecoderFootprint abiDecoderAllocation abiEncoderOpenInput
  abiScratchEncoderContract abiScratchFootprint abiDecoderFrame
  valueEncoding venomState finite_map pred_set list arithmetic

Theorem abi_encoder_envelope_disjoint:
  abi_decoder_budget first last b cap s /\ first <= lo /\ hi <= last /\
  (p+n <= b \/ b+cap <= p) ==>
  abi_footprint_disjoint p n
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)
Proof
  strip_tac >> drule abi_decoder_budget_frontier >> strip_tac >>
  irule abi_decoder_child_scratch_disjoint >> simp[] >>
  rpt strip_tac >>
  `id IN abi_decoder_ids first last` by
    (fs[abi_decoder_ids_def] >> decide_tac) >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_budget_def] >> strip_tac >>
  qpat_x_assum `!id off sz. _ ==> _` drule >> disch_then drule >>
  strip_tac >> decide_tac
QED

Theorem abi_encoder_pre_shared:
  abi_encoder_pre ei at av st src dst sb source_cap d b cap s /\
  abi_decoder_budget first last b cap s ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,LENGTH (enc at av)) (first,last,b,cap) s
Proof
  simp_tac bool_ss [abi_encoder_pre_def, abi_encoder_shared_input_def] >>
  strip_tac >> drule abi_encoder_input_open >> strip_tac >>
  asm_simp_tac (srw_ss()) [venomMemDefsTheory.regions_disjoint_def] >>
  rpt conj_tac >> metis_tac[abi_encoder_envelope_disjoint, LESS_EQ_REFL]
QED

Theorem abi_encoder_scratch_frame_envelope:
  abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t /\
  abi_decoder_budget first last b cap s /\ first <= lo /\ hi <= last ==>
  abi_decode_footprint_frame [(d,sz);(b,cap)] s t
Proof
  strip_tac >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >>
  reverse conj_tac >- fs[abi_decode_footprint_frame_def] >>
  rpt strip_tac >>
  `abi_footprint_disjoint p n
     ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (fs[abi_scratch_disjoint_cons] >>
     metis_tac[abi_encoder_envelope_disjoint, ADD_COMM]) >>
  fs[abi_decode_footprint_frame_def]
QED

Theorem abi_encoder_scratch_effect_envelope:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_budget first last b cap s /\ first <= lo /\ hi <= last /\
  (d+sz <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  strip_tac >>
  `abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    metis_tac[abi_encoder_envelope_disjoint, LESS_EQ_REFL] >>
  `abi_decoder_scratch_frame first last lo hi s t` by
    (simp_tac bool_ss [abi_decoder_scratch_frame_def] >> conj_tac
     >- fs[abi_scratch_effect_def] >> rpt strip_tac >>
     `id IN abi_decoder_ids first last /\ ~(id IN abi_decoder_ids lo hi)` by
       (simp[abi_decoder_ids_def] >> decide_tac) >>
     drule_all abi_scratch_effect_slot >> simp[]) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  simp_tac bool_ss [abi_decoder_effect_def] >>
  asm_simp_tac bool_ss [] >> irule abi_encoder_scratch_frame_envelope >>
  metis_tac[]
QED

Theorem abi_encoder_shared_correct:
  abi_encoder_shared ei ==> abi_encoder_correct ei
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_correct_def] >> rpt strip_tac >>
  drule_all abi_encoder_pre_shared >> strip_tac >>
  `?actual. abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    (first,last,b,cap) (at,av,d) initial actual` by
    (irule abi_encoder_shared_run >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule abi_encoder_shared_endpoint_sim >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_endpoint _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_endpoint_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_scratch_effect_envelope >>
  fs[abi_encoder_pre_def] >> metis_tac[]
QED

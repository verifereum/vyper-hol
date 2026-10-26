(* Restrict physical scratch ownership to a generated child interval.
   TOP-LEVEL: abi_scratch_disjoint_subset protects the same buffer when a child
   owns fewer registered sites and shares the enclosing frontier reserve. *)
Theory abiScratchSubset
Ancestors
  abiScratchFootprint abiDecoderFootprint abiDecoderFrame pred_set list arithmetic

Theorem abi_scratch_disjoint_subset:
  FINITE ids /\ child_ids SUBSET ids /\
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s) ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch child_ids b cap s)
Proof
  strip_tac >> `FINITE child_ids` by
    (irule SUBSET_FINITE_I >> qexists_tac `ids` >> simp[]) >>
  simp_tac bool_ss [abi_footprint_disjoint_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_footprint_disjoint p n _`
    (qspecl_then [`d`, `sz`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  impl_tac >- (fs[abi_decoder_child_scratch_def, MEM_MAP] >>
    rename1 `MEM allocated_id (SET_TO_LIST child_ids)` >>
    disj2_tac >> qexists_tac `allocated_id` >>
    `allocated_id IN child_ids` by
      (drule (Q.SPEC `child_ids` MEM_SET_TO_LIST) >>
       disch_then (qspec_then `allocated_id` mp_tac) >> asm_simp_tac bool_ss []) >>
    fs[MEM_SET_TO_LIST, SUBSET_DEF]) >> simp[]
QED

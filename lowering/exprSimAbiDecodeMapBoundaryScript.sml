(* Pure descending-map boundaries; no execution resources are involved. *)
Theory exprSimAbiDecodeMapBoundary
Ancestors
  abiDecoderCoherence finite_map list

Theorem abi_decoder_coherent_submap:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !sf'. sf SUBMAP sf' ==> abi_decoder_coherent ce env sf' ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt strip_tac >> simp[abi_decoder_coherent_base_iff])
  >- (rpt strip_tac >> simp[abi_decoder_coherent_flag_iff])
  >- (rpt strip_tac >> simp[abi_decoder_coherent_array_iff] >> metis_tac[])
  >- suspend "tuple"
  >> suspend "struct"
QED
Resume abi_decoder_coherent_submap[tuple]:
  rpt strip_tac >> simp[abi_decoder_coherent_tuple_iff] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN]
QED
Resume abi_decoder_coherent_submap[struct]:
  rpt strip_tac >>
  `FLOOKUP sf' (nsid_to_string nsid) = SOME fields` by
    fs[SUBMAP_FLOOKUP_EQN] >>
  `sf \\ nsid_to_string nsid SUBMAP sf' \\ nsid_to_string nsid` by
    fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  simp[abi_decoder_coherent_struct_iff] >>
  qexists_tac `tvs` >> simp[] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[LIST_REL_EL_EQN]
QED
Finalise abi_decoder_coherent_submap

Theorem abi_decoder_coherent_restore_map:
  abi_decoder_coherent ce env (ce.ce_struct_fields \\ key) ty tv ==>
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv
Proof
  strip_tac >> drule abi_decoder_coherent_submap >>
  disch_then irule >>
  simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >> metis_tac[]
QED

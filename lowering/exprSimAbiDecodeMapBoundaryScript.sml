(* Pure descending-map boundaries; no execution resources are involved. *)
Theory exprSimAbiDecodeMapBoundary
Ancestors
  abiDecoderCoherence abiDecoderMemberInfos exprLowering finite_map list

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

Theorem abi_decoder_descriptor_submap:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !sf'. sf SUBMAP sf' ==>
    type_to_abi_dec_info sf ce ty = type_to_abi_dec_info sf' ce ty
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
  >- (rpt strip_tac >> simp[type_to_abi_dec_info_def])
  >- (rpt strip_tac >>
      `type_to_abi_dec_info sf ce ty = type_to_abi_dec_info sf' ce ty` by metis_tac[] >>
      Cases_on `bound` >> simp[type_to_abi_dec_info_def])
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_decoder_descriptor_submap[tuple]:
  rpt strip_tac >> simp[type_to_abi_dec_info_def] >>
  irule MAP_CONG >> simp[] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]
QED

Resume abi_decoder_descriptor_submap[struct]:
  rpt strip_tac >>
  `FLOOKUP sf' (nsid_to_string nsid) = SOME fields` by
    fs[SUBMAP_FLOOKUP_EQN] >>
  `sf \\ nsid_to_string nsid SUBMAP sf' \\ nsid_to_string nsid` by
    fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  simp[type_to_abi_dec_info_def] >>
  irule MAP_CONG >> simp[] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> gen_tac >> strip_tac >>
  PairCases_on `x` >> simp[] >>
  `MEM x1 (MAP SND args)` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists `(x0,x1)` >> simp[] >>
     qexists `(x0,x1,x2)` >> simp[]) >>
  metis_tac[MEM_EL, LENGTH_MAP]
QED

Finalise abi_decoder_descriptor_submap

Theorem abi_decoder_member_infos_submap:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ sf SUBMAP sf' ==>
  abi_decoder_member_infos sf ce tys = abi_decoder_member_infos sf' ce tys
Proof
  strip_tac >> simp[abi_decoder_member_infos_def] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >>
  metis_tac[MEM_EL, abi_decoder_descriptor_submap]
QED

Theorem abi_decoder_descriptor_restore_map:
  abi_decoder_coherent ce env (ce.ce_struct_fields \\ key) ty tv ==>
  type_to_abi_dec_info (ce.ce_struct_fields \\ key) ce ty =
    type_to_abi_dec_info ce.ce_struct_fields ce ty
Proof
  strip_tac >> drule abi_decoder_descriptor_submap >> disch_then irule >>
  simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >> metis_tac[]
QED

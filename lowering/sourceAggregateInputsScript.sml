(* Pure aggregate views and memory assembly for the source decoder fold. *)
Theory sourceAggregateInputs
Ancestors
  sourceArrayInputs abiDecoderMemberInfos sourceEncodingLayout abiDecoderCoherence
  typedCopyTuplePtr valueEncodingProofs placeMemoryTypedBase
  vyperTyping vyperABI vyperABIRoundtrip vyperTypeDefaults list rich_list

Theorem source_tuple_values:
  value_has_type (TupleTV tvs) v /\
  vyper_to_abi env (TupleT tys) v = SOME av ==>
  ?vs avs. v = ArrayV (TupleV vs) /\ av = ListV avs /\
    LIST_REL value_has_type tvs vs /\
    vyper_to_abi_list env tys vs = SOME avs
Proof
  strip_tac >>
  `?vs. v = ArrayV (TupleV vs)` by
    (qpat_assum `value_has_type _ v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `v` >> simp[value_has_type_def] >>
     rename1 `ArrayV a` >> Cases_on `a` >> simp[value_has_type_def]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  gvs[value_has_type_def, vyper_to_abi_def, AllCaseEqs(),
    values_have_types_LIST_REL] >> metis_tac[]
QED

Theorem source_struct_values:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH args = LENGTH tvs /\
  value_has_type (StructTV (ZIP (MAP FST args,tvs))) v /\
  vyper_to_abi env (StructT nsid) v = SOME av ==>
  ?fields avs. v = StructV fields /\ av = ListV avs /\
    LIST_REL value_has_type tvs (MAP SND fields) /\
    vyper_to_abi_list (env \\ nsid) (MAP SND args) (MAP SND fields) = SOME avs
Proof
  strip_tac >>
  `?fields. v = StructV fields` by
    (qpat_assum `value_has_type _ v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `v` >>
     simp[value_has_type_def] >> rename1 `ArrayV a` >>
     Cases_on `a` >> simp[value_has_type_def]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `LIST_REL value_has_type tvs (MAP SND fields)` by
    (qpat_x_assum `value_has_type _ _` mp_tac >>
     simp[value_has_type_def] >>
     disch_then (mp_tac o MATCH_MP struct_has_type_values_have_types) >>
     simp[MAP_ZIP, values_have_types_LIST_REL]) >>
  qpat_x_assum `vyper_to_abi env _ _ = _` mp_tac >>
  simp[vyper_to_abi_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem coherent_member_infos_indexed:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  LENGTH (abi_decoder_member_infos sf ce tys) = LENGTH tys /\
  (!i. i < LENGTH tys ==>
    EL i (abi_decoder_member_infos sf ce tys) =
      (type_to_abi_dec_info sf ce (EL i tys),
       abi_member_head_size (EL i (MAP (vyper_to_abi_type env) tys)),
       type_memory_size (EL i tvs)))
Proof
  strip_tac >> simp[abi_decoder_member_infos_def, EL_MAP] >>
  rpt strip_tac >>
  `abi_decoder_coherent ce env sf (EL i tys) (EL i tvs)` by
    metis_tac[LIST_REL_EL_EQN] >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]
QED

Theory exprSimAbiDecodeRecursiveClosure
Ancestors
  exprSimAbiDecodeConstructorOutcome exprSimAbiDecodePrimitiveOwned
  exprSimAbiDecodeFixedArrayOwned exprSimAbiDecodeBulkOwned
  exprSimAbiDecodeArrayClosure abiDecoderCoherence exprSimAbiDecodeOwnedContext
  exprLowering vyperTypeSystem vyperValue finite_map list rich_list
  exprSimAbiDecodeMapBoundary

Theorem abi_decode_owned_coherence_induction:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    (sf SUBMAP ce.ce_struct_fields /\ assignable_type env ty /\
     abi_decode_bytes_widths env ty ==>
     !tv'. abi_decoder_coherent ce env ce.ce_struct_fields ty tv' ==>
       abi_decode_owned_child_contract ce env ty tv')
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED
Resume abi_decode_owned_coherence_induction[base]:
  rpt strip_tac >>
  gvs[Once abi_decoder_coherent_cases] >> irule abi_decode_base_owned_contract
QED
Resume abi_decode_owned_coherence_induction[flag]:
  rpt strip_tac >>
  gvs[Once abi_decoder_coherent_cases] >> irule abi_decode_flag_owned_contract
QED
Resume abi_decode_owned_coherence_induction[array]:
  rpt strip_tac >>
  `assignable_type env ty /\ abi_decode_bytes_widths env ty` by
    fs[assignable_type_def, abi_decode_bytes_widths_def] >>
  `!tv'. abi_decoder_coherent ce env ce.ce_struct_fields ty tv' ==>
    abi_decode_owned_child_contract ce env ty tv'` by metis_tac[] >>
  Cases_on `bound`
  >- (irule abi_decode_fixed_array_owned_contract >> asm_rewrite_tac[]) >>
  gvs[abi_decoder_coherent_array_iff] >>
  rename1 `abi_decoder_coherent ce env ce.ce_struct_fields ty child_tv` >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty)`
  >- (irule abi_decode_owned_dynamic_array_nonbulk >>
      drule abi_decoder_coherent_header >>
      simp[abi_decoder_header_def] >> strip_tac >>
      simp[type_to_abi_dec_info_def] >> metis_tac[]) >>
  irule abi_decode_array_bulk_owned_contract >> gvs[]
QED
Resume abi_decode_owned_coherence_induction[tuple]:
  rpt strip_tac >> irule abi_decode_tuple_owned_contract >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `!ty. MEM ty tys ==> assignable_type env ty /\ abi_decode_bytes_widths env ty` by
    (fs[assignable_type_def, abi_decode_bytes_widths_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `?i. i < LENGTH tys /\ EL i tys = ty` by metis_tac[MEM_EL] >>
  first_x_assum (qspec_then `i` mp_tac) >> asm_rewrite_tac[] >> metis_tac[]
QED
Resume abi_decode_owned_coherence_induction[struct]:
  rpt strip_tac >>
  `FLOOKUP ce.ce_struct_fields (nsid_to_string nsid) = SOME fields` by
    fs[SUBMAP_FLOOKUP_EQN] >>
  `sf \\ nsid_to_string nsid SUBMAP ce.ce_struct_fields` by
    (fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  irule abi_decode_struct_owned_contract >>
  asm_rewrite_tac[] >> qexists `fields` >> asm_rewrite_tac[] >> rpt strip_tac >>
  `abi_decoder_coherent ce (env \\ nsid) ce.ce_struct_fields ty tv` by
    metis_tac[abi_decoder_coherent_restore_map] >>
  `!ty. MEM ty (MAP SND args) ==> assignable_type (env \\ nsid) ty /\
    abi_decode_bytes_widths (env \\ nsid) ty` by
    (gvs[assignable_type_def, abi_decode_bytes_widths_def, EVERY_MEM, MEM_MAP] >>
     metis_tac[]) >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  `MEM ty (MAP SND args)` by metis_tac[] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[LIST_REL_EL_EQN] >> strip_tac >>
  `?i. i < LENGTH (MAP SND args) /\ EL i (MAP SND args) = ty` by metis_tac[MEM_EL] >>
  first_x_assum (qspec_then `i` mp_tac) >> asm_rewrite_tac[] >>
  gvs[LENGTH_MAP] >> metis_tac[]
QED
Finalise abi_decode_owned_coherence_induction

Theorem abi_decode_owned_recursive_contract:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty ==>
  abi_decode_owned_child_contract ce env ty tv
Proof
  strip_tac >> drule abi_decode_owned_coherence_induction >>
  simp[SUBMAP_REFL] >> disch_then irule >> asm_rewrite_tac[]
QED

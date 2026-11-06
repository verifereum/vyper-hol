Theory exprSimAbiDecodeConstructorRows
Ancestors
  exprSimAbiDecodeComplexOutcome exprSimAbiDecodeWidthBoundary
  exprSimAbiDecodeMapBoundary exprSimAbiDecodeTupleAssembly
  exprSimAbiDecodeTupleOutcome abiDecoderCoherence abiDecoderMemberInfos
  abiDecodeRanges valueEncoding compileEnv vyperTypeSystem vyperValue
  finite_map list arithmetic

Theorem abi_decode_tuple_pure_rows:
  abi_decoder_coherent ce env ce.ce_struct_fields (TupleT tys) atv /\
  assignable_type env (TupleT tys) /\ abi_decode_bytes_widths env (TupleT tys) ==>
  ?rows. abi_tuple_rows_schema ce env rows /\
    tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
    atv = TupleTV (MAP (\(ei,ty,tv,asz,msz). tv) rows) /\
    type_to_abi_dec_info ce.ce_struct_fields ce (TupleT tys) =
      DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
        (MAP abi_tuple_row_code rows) /\
    SUM (MAP abi_tuple_row_mem_width rows) = type_memory_bytes ce (TupleT tys) /\
    SUM (MAP abi_tuple_row_abi_width rows) <= SUM (MAP abi_tuple_row_mem_width rows)
Proof
  strip_tac >> drule_all abi_decode_tuple_constructor_rows >> strip_tac >>
  qexists `rows` >>
  drule abi_decode_schema_rows_layout >> strip_tac >>
  drule abi_tuple_rows_head_le_memory >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  gvs[type_memory_size_def] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> PairCases_on `x` >>
  simp[abi_tuple_row_code_def]
QED

Theorem abi_decode_struct_pure_rows:
  abi_decoder_coherent ce env ce.ce_struct_fields (StructT nsid) atv /\
  assignable_type env (StructT nsid) /\ abi_decode_bytes_widths env (StructT nsid) ==>
  ?args fields rows.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP ce.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
    args = MAP (\(name,ty,sz). (name,ty)) fields /\
    abi_tuple_rows_schema ce (env \\ nsid) rows /\
    MAP (\(ei,ty,tv,asz,msz). ty) rows = MAP (FST o SND) fields /\
    atv = StructTV (ZIP (MAP FST args,MAP (\(ei,ty,tv,asz,msz). tv) rows)) /\
    LIST_REL (abi_decoder_coherent ce (env \\ nsid)
      (ce.ce_struct_fields \\ nsid_to_string nsid))
      (MAP (\(ei,ty,tv,asz,msz). ty) rows)
      (MAP (\(ei,ty,tv,asz,msz). tv) rows) /\
    MAP abi_tuple_row_code rows = abi_decoder_member_infos
      (ce.ce_struct_fields \\ nsid_to_string nsid) ce (MAP (FST o SND) fields) /\
    SUM (MAP abi_tuple_row_abi_width rows) <= SUM (MAP abi_tuple_row_mem_width rows)
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_struct_iff] >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND args) /\
   EVERY (abi_decode_bytes_widths (env \\ nsid)) (MAP SND args)` by
    (qpat_x_assum `assignable_type env (StructT nsid)` mp_tac >>
     qpat_x_assum `abi_decode_bytes_widths env (StructT nsid)` mp_tac >>
     asm_simp_tac (srw_ss()) [assignable_type_def, abi_decode_bytes_widths_def,
       EVERY_MAP, combinTheory.o_DEF]) >>
  `LIST_REL (abi_decoder_coherent ce (env \\ nsid) ce.ce_struct_fields)
    (MAP SND args) tvs` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     simp[LIST_REL_EL_EQN] >> metis_tac[abi_decoder_coherent_restore_map]) >>
  drule_all abi_decode_constructor_rows_exist >> strip_tac >>
  `MAP SND args = MAP (FST o SND) fields` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o] >> irule MAP_CONG >> simp[] >>
     rpt strip_tac >> PairCases_on `x` >> simp[]) >>
  `abi_decoder_member_infos (ce.ce_struct_fields \\ nsid_to_string nsid) ce
      (MAP SND args) = abi_decoder_member_infos ce.ce_struct_fields ce (MAP SND args)` by
    (irule abi_decoder_member_infos_submap >> conj_tac
     >- (simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
     qexistsl_tac [`env \\ nsid`, `tvs`] >> asm_rewrite_tac []) >>
  `MAP abi_tuple_row_code rows = MAP (\(ei,ty,tv,asz,msz). (ei,asz,msz)) rows` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >> PairCases_on `x` >>
     simp[abi_tuple_row_code_def]) >>
  drule abi_tuple_rows_head_le_memory >> strip_tac >>
  qexistsl_tac [`args`, `fields`, `rows`] >> asm_rewrite_tac [] >> metis_tac[]
QED

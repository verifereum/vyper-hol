Theory entrySupportedAbiWidths
Ancestors supportedTypes vyperTypeSystem vyperABI list finite_map pair arithmetic combin

Theorem supported_assignable_abi_widths:
  !env ty. assignable_type env ty ==> !tops fuel.
    (!id fields. FLOOKUP env id = SOME (StructArgs fields) ==>
       supported_struct_fields tops id = SOME fields) /\
    supported_nested_type supported_scalar_type fuel tops ty ==>
    abi_decode_bytes_widths env ty
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >~ [`abi_decode_bytes_widths env (BaseT bt)`] >-
    (rpt strip_tac >> Cases_on `bt` >>
     gvs[Once supported_nested_type_def, supported_scalar_type_def,
         supported_word_type_def, supported_string_type_def,
         abi_decode_bytes_widths_def] >>
     Cases_on `b` >> gvs[supported_word_type_def, supported_string_type_def])
  >~ [`abi_decode_bytes_widths env (TupleT tys)`] >-
    (rpt strip_tac >>
     qpat_x_assum `supported_nested_type _ _ _ (TupleT _)` mp_tac >>
     simp[Once supported_nested_type_def, supported_scalar_type_def,
          supported_word_type_def, supported_string_type_def] >> strip_tac >>
     gvs[Once assignable_type_def, abi_decode_bytes_widths_def, EVERY_MEM] >>
     metis_tac[])
  >~ [`abi_decode_bytes_widths env (ArrayT ty bd)`] >-
    (rpt strip_tac >>
     qpat_x_assum `supported_nested_type _ _ _ (ArrayT _ _)` mp_tac >>
     Cases_on `bd` >>
     simp[Once supported_nested_type_def, supported_scalar_type_def,
          supported_word_type_def, supported_string_type_def] >> strip_tac >>
     gvs[Once assignable_type_def, abi_decode_bytes_widths_def] >>
     metis_tac[])
  >~ [`abi_decode_bytes_widths env (FlagT id)`] >-
    simp[abi_decode_bytes_widths_def]
  >~ [`abi_decode_bytes_widths env NoneT`] >-
    simp[abi_decode_bytes_widths_def] >>
  rpt strip_tac >>
  gvs[Once assignable_type_def] >>
  Cases_on `FLOOKUP env nsid` >> gvs[] >>
  Cases_on `x` >> gvs[] >> rename1 `StructArgs args` >>
  `supported_struct_fields tops nsid = SOME args` by metis_tac[] >>
  qpat_x_assum `supported_nested_type _ _ _ (StructT _)` mp_tac >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac >>
  gvs[abi_decode_bytes_widths_def, EVERY_MEM, o_DEF] >>
  `!id fields. FLOOKUP (env \\ nsid) id = SOME (StructArgs fields) ==>
     supported_struct_fields tops id = SOME fields` by
    (simp[DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  metis_tac[]
QED

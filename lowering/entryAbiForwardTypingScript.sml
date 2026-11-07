Theory entryAbiForwardTyping
Ancestors
  entryAbiScalarTyping entryAbiArrayTyping entryAbiTupleTyping entryAbiStructTyping
  entryHereditarySlotCardinality vyperTypeSystem vyperTyping vyperABI
  vyperValue contractABI list finite_map pair

Theorem entry_assignable_abi_conversion_typed:
  !env ty. assignable_type env ty ==> !tv v av.
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    abi_decode_bytes_widths env ty /\
    entry_tuple_cardinality (vyper_to_abi_type env ty) /\
    vyper_to_abi env ty v = SOME av ==>
    has_type (vyper_to_abi_type env ty) av
Proof
  ho_match_mp_tac assignable_type_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [`evaluate_type env (BaseT bt) = _`] >-
    (rpt strip_tac >> irule entry_base_abi_conversion_typed >> metis_tac[])
  >~ [`evaluate_type env (FlagT nsid) = _`] >-
    (rpt strip_tac >> irule entry_flag_abi_conversion_typed >> metis_tac[])
  >~ [`evaluate_type env NoneT = _`] >- gvs[assignable_type_def]
  >~ [`assignable_type env (TupleT tys) ==> _`] >-
    (rpt strip_tac >> irule entry_tuple_abi_conversion_typed >>
     simp[] >> gvs[Once assignable_type_def, EVERY_MEM] >> metis_tac[])
  >~ [`assignable_type env (ArrayT ty bd) ==> _`] >-
    (rpt strip_tac >> irule entry_array_abi_conversion_typed >>
     simp[] >> gvs[Once assignable_type_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `?fields. FLOOKUP env nsid = SOME (StructArgs fields) /\
    EVERY (assignable_type (env \\ nsid) o SND) fields` by
    (gvs[Once assignable_type_def] >>
     Cases_on `FLOOKUP env nsid` >> gvs[] >>
     Cases_on `x` >> gvs[EVERY_MEM]) >>
  irule entry_struct_abi_conversion_typed >> simp[] >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

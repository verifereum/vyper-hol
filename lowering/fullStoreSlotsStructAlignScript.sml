(* Typed struct metadata for an arbitrary recursive execution relation. *)
Theory fullStoreSlotsStructAlign
Ancestors
  placeStoreSlots typedMemoryCopy typedCopyDomain exprSimProps valueEncodingTyping
  context compileEnv vyperTyping vyperTypeValues vyperValue valueEncodingProps
  vyperTypeExprSoundness vyperTypeABI list rich_list finite_map
  loweringStateRelDefs placeStoreStorage

Theorem store_slots_fields_align_full[local]:
  !fields tvs vs.
  OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
  values_have_types tvs vs /\
  EVERY (\(fname,fty,sz). !tv.
    evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields /\
  (!fname ty sz tv v. MEM (fname,ty,sz) fields /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==> R ty tv v) ==>
  LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\ R ty tv v /\
    IS_SOME (encode_value tv v) /\ val_store_size tv v <= type_memory_size tv)
    (MAP SND fields) (ZIP (tvs,vs))
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> Cases_on `vs` >> gvs[value_has_type_def]) >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `vs` >> gvs[value_has_type_def] >>
  simp[] >> conj_tac
  >- metis_tac[value_has_type_equiv, val_store_size_le, cj 1 value_has_type_val_wf] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem store_slots_struct_align_full:
  !cenv tenv nsid tv v.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  evaluate_type tenv (StructT nsid) = SOME tv /\ value_has_type tv v /\
  (!cty ctv cv. type_rank cenv.ce_struct_fields cty <
     type_rank cenv.ce_struct_fields (StructT nsid) /\
     evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==> R cty ctv cv) ==>
  ?fields tvs vals.
    FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
    tv = StructTV (ZIP (MAP FST fields,tvs)) /\ v = StructV vals /\
    LENGTH fields = LENGTH tvs /\ LENGTH vals = LENGTH tvs /\
    LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\ R ty tv v /\
      IS_SOME (encode_value tv v) /\ val_store_size tv v <= type_memory_size tv)
      (MAP SND fields) (ZIP (tvs,MAP SND vals))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv nsid = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >> drule OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `struct_has_type _ vals` >>
  `fields_val_wf vals (ZIP (MAP FST args,tvs))` by
    metis_tac[cj 5 value_has_type_val_wf] >>
  `values_have_types tvs (MAP SND vals) /\ LENGTH vals = LENGTH tvs` by
    metis_tac[place_store_struct_tuple_values, LENGTH_MAP] >>
  qexists_tac `tvs` >> simp[] >>
  conj_tac >- metis_tac[LENGTH_MAP] >>
  irule store_slots_fields_align_full >> simp[] >> qexists_tac `tenv` >>
  fs[evaluate_types_OPT_MMAP] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
      once_rewrite_tac[type_rank_nsid] >> irule member_rank_lt_struct >>
      simp[get_struct_fields_def] >> metis_tac[]) >>
  metis_tac[]
QED

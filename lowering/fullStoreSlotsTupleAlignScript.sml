(* Typed tuple metadata, independently of the sparse execution relation. *)
Theory fullStoreSlotsTupleAlign
Ancestors
  placeStoreSlots typedMemoryCopy exprSimProps valueEncodingTyping
  context compileEnv vyperTyping vyperTypeValues vyperValue valueEncodingProps
  list rich_list finite_map vyperTypeDefaults typedCopyDomain

Theorem store_slots_tuple_align:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  evaluate_type tenv (TupleT tys) = SOME tv /\ value_has_type tv v /\
  (!cty ctv cv.
    type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields (TupleT tys) /\
    evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==> R cty ctv cv) ==>
  ?tvs vs. tv = TupleTV tvs /\ v = ArrayV (TupleV vs) /\
    LENGTH tys = LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
    LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\ R ty tv v /\
      IS_SOME (encode_value tv v) /\ val_store_size tv v <= type_memory_size tv)
      (MAP (\ty. (ty,type_memory_bytes cenv ty)) tys) (ZIP (tvs,vs))
Proof
  strip_tac >> drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `values_have_types tvs vs` >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >> rpt strip_tac >>
  rename1 `idx < LENGTH tvs` >>
  `evaluate_type tenv (EL idx tys) = SOME (EL idx tvs)` by metis_tac[] >>
  `value_has_type (EL idx tvs) (EL idx vs)` by metis_tac[] >>
  rpt conj_tac
  >- (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >- (first_x_assum irule >> simp[] >> irule member_rank_lt_tuple >> simp[EL_MEM])
  >- metis_tac[value_has_type_equiv] >>
  metis_tac[val_store_size_le, cj 1 value_has_type_val_wf]
QED

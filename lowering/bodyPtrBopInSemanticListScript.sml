Theory bodyPtrBopInSemanticList
Ancestors bodyPtrBopInSourceTyping vyperValueOperation vyperTyping
  entryDecodeStaticProps list rich_list valueEncoding abiStaticSparseProps
  pred_set alist pair

Theorem membership_map_reflects:
  (!x. MEM x xs ==> (f needle = f x <=> needle = x)) ==>
  (MEM (f needle) (MAP f xs) <=> MEM needle xs)
Proof
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem membership_dynamic_encoded_mem:
  is_word_type et /\ evaluate_type tenv et = SOME tv /\
  value_has_type tv needle /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) ==>
  (MEM (typed_val_to_w256 tv needle) (MAP (typed_val_to_w256 tv) vs) <=>
   MEM needle vs)
Proof
  strip_tac >> irule membership_map_reflects >> rpt strip_tac >>
  drule_all membership_array_encoding_reflects >>
  simp[] >> strip_tac >>
  gvs[MEM_EL] >> metis_tac[]
QED

Theorem membership_dynamic_source_encoded:
  is_word_type et /\ evaluate_type tenv et = SOME tv /\
  value_has_type tv needle /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  (bop = In \/ bop = NotIn) ==>
  evaluate_binop u (ArrayTV tv (Dynamic cap)) bop needle (ArrayV (DynArrayV vs)) =
    INL (BoolV (if bop = In then
      MEM (typed_val_to_w256 tv needle) (MAP (typed_val_to_w256 tv) vs)
    else ~MEM (typed_val_to_w256 tv needle) (MAP (typed_val_to_w256 tv) vs)))
Proof
  strip_tac >> drule_all membership_dynamic_encoded_mem >>
  simp[Once evaluate_binop_def, evaluate_in_array_def, binop_negate_def] >>
  simp[Once evaluate_binop_def, evaluate_in_array_def, binop_negate_def]
QED

Theorem membership_sparse_missing:
  sparse_has_type tv cap kvs /\ SORTED $< (MAP FST kvs) ==>
  ((?i. i < cap /\ ALOOKUP kvs i = NONE) <=> LENGTH kvs < cap)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST kvs)` by metis_tac[SORTED_lt_ALL_DISTINCT] >>
  `CARD (set (MAP FST kvs)) = LENGTH kvs` by
    simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `set (MAP FST kvs) SUBSET count cap` by
    (simp[SUBSET_DEF, MEM_MAP] >> rpt strip_tac >>
     PairCases_on `y` >> gvs[] >> metis_tac[typed_sparse_key_bound]) >>
  eq_tac
  >- (strip_tac >>
      `set (MAP FST kvs) PSUBSET count cap` by
        (simp[PSUBSET_MEMBER] >> qexists_tac `i` >>
         gvs[ALOOKUP_NONE]) >>
      `CARD (set (MAP FST kvs)) < CARD (count cap)` by
        (irule CARD_PSUBSET >> simp[]) >> gvs[]) >>
  strip_tac >> spose_not_then assume_tac >>
  `set (MAP FST kvs) = count cap` by
    (gvs[ALOOKUP_NONE, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  qpat_x_assum `CARD _ = LENGTH _` mp_tac >> simp[]
QED

Theorem membership_sparse_values:
  sparse_has_type tv cap kvs /\ SORTED $< (MAP FST kvs) ==>
  (MEM needle (GENLIST (sparse_val tv kvs) cap) <=>
   MEM needle (MAP SND kvs) \/
   (LENGTH kvs < cap /\ needle = default_value tv))
Proof
  strip_tac >>
  `MEM needle (MAP SND kvs) <=>
     ?i. i < cap /\ ALOOKUP kvs i = SOME needle` by
    (simp[MEM_MAP, EXISTS_PROD] >>
     metis_tac[sorted_sparse_ALOOKUP, ALOOKUP_MEM, typed_sparse_key_bound]) >>
  drule_all membership_sparse_missing >>
  simp[MEM_GENLIST, sparse_val_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem membership_fixed_encoded_mem:
  is_word_type et /\ evaluate_type tenv et = SOME tv /\
  value_has_type tv needle /\
  value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) ==>
  (MEM (typed_val_to_w256 tv needle)
     (GENLIST (\i. typed_val_to_w256 tv (sparse_val tv kvs i)) cap) <=>
   MEM needle (GENLIST (sparse_val tv kvs) cap))
Proof
  strip_tac >>
  `MEM (typed_val_to_w256 tv needle)
     (MAP (typed_val_to_w256 tv) (GENLIST (sparse_val tv kvs) cap)) <=>
   MEM needle (GENLIST (sparse_val tv kvs) cap)` by
    (irule membership_map_reflects >> simp[MEM_GENLIST] >>
     rpt strip_tac >>
     drule_all membership_array_encoding_reflects >> simp[] >>
     metis_tac[]) >>
  gvs[MAP_GENLIST, combinTheory.o_DEF]
QED

Theorem membership_fixed_source_encoded:
  is_word_type et /\ evaluate_type tenv et = SOME tv /\
  value_has_type tv needle /\
  value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
  (bop = In \/ bop = NotIn) ==>
  evaluate_binop u (ArrayTV tv (Fixed cap)) bop needle (ArrayV (SArrayV kvs)) =
    INL (BoolV (if bop = In then
      MEM (typed_val_to_w256 tv needle)
        (GENLIST (\i. typed_val_to_w256 tv (sparse_val tv kvs i)) cap)
    else ~MEM (typed_val_to_w256 tv needle)
        (GENLIST (\i. typed_val_to_w256 tv (sparse_val tv kvs i)) cap)))
Proof
  strip_tac >> drule_all membership_fixed_encoded_mem >>
  `sparse_has_type tv cap kvs /\ SORTED $< (MAP FST kvs)` by
    gvs[value_has_type_def] >>
  drule_all membership_sparse_values >>
  simp[Once evaluate_binop_def, evaluate_in_array_def, binop_negate_def] >>
  simp[Once evaluate_binop_def, evaluate_in_array_def, binop_negate_def]
QED

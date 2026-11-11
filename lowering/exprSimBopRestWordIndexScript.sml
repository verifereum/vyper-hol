(* Indexed source-array membership, including sparse defaults. *)
Theory exprSimBopRestWordIndex
Ancestors
  vyperArray vyperTyping vyperValueOperation pred_set list sorting alist
  compileEnv valueEncodingProps valueEncoding vyperValue vyperStorage
  vyperAssignPreservesType exprSimBopInLiteralWord

Theorem rest_word_missing_index[local]:
  ALL_DISTINCT ks /\ EVERY (\k. k < n) ks ==>
  (LENGTH ks < n <=> ?i. i < n /\ ~MEM i ks)
Proof
  strip_tac >>
  `set ks SUBSET count n` by
    gvs[SUBSET_DEF, EVERY_MEM] >>
  `CARD (set ks) = LENGTH ks` by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  eq_tac
  >- (strip_tac >> spose_not_then assume_tac >>
      `count n SUBSET set ks` by gvs[SUBSET_DEF] >>
      `CARD (count n) <= CARD (set ks)` by
        (irule CARD_SUBSET >> simp[]) >>
      gvs[]) >>
  strip_tac >>
  `i INSERT set ks SUBSET count n` by simp[INSERT_SUBSET] >>
  `CARD (i INSERT set ks) <= CARD (count n)` by
    (irule CARD_SUBSET >> simp[]) >>
  gvs[]
QED

Theorem rest_word_sparse_membership:
  ALL_DISTINCT (MAP FST al) /\ EVERY (\kv. FST kv < n) al ==>
  (evaluate_in_array (ArrayTV et (Fixed n)) v (SArrayV al) <=>
   ?i. i < n /\ array_index (ArrayTV et (Fixed n)) (SArrayV al) (&i) = SOME v)
Proof
  strip_tac >>
  `LENGTH al < n <=> ?i. i < n /\ ~MEM i (MAP FST al)` by
    (drule rest_word_missing_index >> simp[EVERY_MAP]) >>
  simp[evaluate_in_array_def, array_index_def] >>
  eq_tac
  >- (strip_tac
      >- (gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
          rename1 `MEM (k,v) al` >> qexists_tac `k` >>
          `k < n` by (gvs[EVERY_MEM] >> metis_tac[pairTheory.FST]) >>
          `ALOOKUP al k = SOME v` by
            metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >> simp[]) >>
      qexists_tac `i` >>
      `ALOOKUP al i = NONE` by simp[alistTheory.ALOOKUP_NONE] >> simp[]) >>
  strip_tac >>
  gvs[AllCaseEqs()]
  >- (disj2_tac >> qexists_tac `i` >> gvs[alistTheory.ALOOKUP_NONE]) >>
  disj1_tac >> drule alistTheory.ALOOKUP_MEM >>
  strip_tac >> simp[MEM_MAP] >> qexists_tac `(i,v)` >> simp[]
QED

Theorem rest_word_list_membership:
  evaluate_in_array tv v (DynArrayV vs) <=>
  ?i. i < array_length tv (DynArrayV vs) /\
      array_index tv (DynArrayV vs) (&i) = SOME v
Proof
  simp[evaluate_in_array_def, array_length_def, array_index_def,
       oEL_THM, MEM_EL] >> metis_tac[]
QED

Theorem rest_word_array_membership:
  value_has_type (ArrayTV et bd) (ArrayV av) ==>
  (evaluate_in_array (ArrayTV et bd) v av <=>
   ?i. i < array_length (ArrayTV et bd) av /\
       array_index (ArrayTV et bd) av (&i) = SOME v)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, rest_word_list_membership] >> strip_tac >>
  simp[array_length_def] >> irule rest_word_sparse_membership >>
  conj_tac >- (irule SORTED_lt_ALL_DISTINCT >> simp[]) >>
  drule sparse_has_type_all_less >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD]
QED

Theorem rest_word_array_word_membership:
  is_word_type ty /\ evaluate_type tenv ty = SOME et /\
  value_has_type et v /\ value_has_type (ArrayTV et bd) (ArrayV av) ==>
  (evaluate_in_array (ArrayTV et bd) v av <=>
   ?i x. i < array_length (ArrayTV et bd) av /\
         array_index (ArrayTV et bd) av (&i) = SOME x /\
         typed_val_to_w256 et x = typed_val_to_w256 et v)
Proof
  strip_tac >> drule rest_word_array_membership >>
  disch_then (qspec_then `v` SUBST1_TAC) >> eq_tac
  >- (strip_tac >> qexistsl_tac [`i`, `v`] >> simp[]) >>
  strip_tac >> qexists_tac `i` >> simp[] >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et x` by (irule array_index_has_type >> metis_tac[]) >>
  `x = v` by metis_tac[literal_typed_encoding_11] >> simp[]
QED

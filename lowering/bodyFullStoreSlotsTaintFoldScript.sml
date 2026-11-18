Theory bodyFullStoreSlotsTaintFold
Ancestors
  lowerDloadMaskedStorage rich_list ptrDiscipline pred_set words

Theorem store_slots_taint_fold_mono:
  !ks X Y k b M.
    X SUBSET Y ==>
    FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) X ks SUBSET
    FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) Y ks
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule ld_key_update_mono >> simp[]
QED

Theorem store_slots_taint_count_fold:
  !n X (k:bytes32) b M. n < dimword(:256) ==>
    FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i)))
      X (COUNT_LIST n) =
    (X DIFF {(k+n2w i,j) | (i,j) | i<n}) UNION
    {(k+n2w i,j) | (i,j) | i<n /\ j<32 /\ b+32*i+j IN M}
Proof
  Induct >> simp[COUNT_LIST_SNOC, FOLDL_SNOC] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`X`,`k`,`b`,`M`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  `!i. i < n ==> (k+n2w i <> k+n2w n)` by
    (rpt strip_tac >>
     gvs[wordsTheory.n2w_11,
         arithmeticTheory.LESS_MOD]) >>
  simp[key_update_def, mem_word_taint_def, EXTENSION,
       pairTheory.FORALL_PROD, PULL_EXISTS, prim_recTheory.LESS_THM] >>
  metis_tac[]
QED

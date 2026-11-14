(* Sparse storage updates retain the allocation frontier. *)
Theory bodyIntCallFamStmtMutationAppendAggregateCopy
Ancestors
  placeStoreSlots stmtSimStoreCopy venomState list words

Theorem intcall_store_slots_normalize_frontier:
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
             (mload (w2n sw + 32*j) s) q) s ks ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  `!ks a. (FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32*j) s) q) a ks).vs_alloca_next =
           a.vs_alloca_next` by
    (Induct >> simp[FOLDL] >> gen_tac >> Cases_on `tr` >>
     gvs[sstore_def,tstore_def]) >>
  disch_then (mp_tac o AP_TERM ``\u:venom_state. u.vs_alloca_next``) >>
  simp[store_copy_normalize_def]
QED

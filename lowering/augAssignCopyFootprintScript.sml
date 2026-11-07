(* Pointwise effects on the identical normalized compiler execution. *)
Theory augAssignCopyFootprint
Ancestors
  placeDynStorageEffect placeStoreStorage placeStoreCopyPath stmtSimStoreCopy
  abiDecodeStaticProps venomState vyperStorage words list rich_list combin arithmetic

Theorem copy_prefix_lookup:
  w2n k + n <= dimword (:256) ==>
  lookup_storage q
    (FOLDL (\st i. update_storage (k+n2w i) (ws i) st)
      st (COUNT_LIST n)) =
  if w2n k <= w2n q /\ w2n q < w2n k+n
  then ws (w2n q-w2n k) else lookup_storage q st
Proof
  strip_tac >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k+n`
  >- (simp[] >>
      qspecl_then [`MAP (\i. (k+n2w i,ws i)) (COUNT_LIST n)`,
        `q`, `ws (w2n q-w2n k)`, `st`] mp_tac place_store_updates_hit >>
      simp[FOLDL_MAP] >> impl_tac >- (conj_tac
      >- (simp[MEM_MAP, MEM_COUNT_LIST] >>
          qexists `w2n q-w2n k` >>
          `w2n k + (w2n q-w2n k) = w2n q` by decide_tac >>
          `k + n2w (w2n q-w2n k) = q` by
            (metis_tac[word_add_n2w, n2w_w2n]) >>
          simp[] >> decide_tac) >>
      simp[MEM_MAP, MEM_COUNT_LIST, PULL_EXISTS] >>
      rpt strip_tac >> gvs[] >> rename1 `ws j = _` >>
      `w2n (k+n2w j) = w2n k+j` by
        (irule w2n_add_n2w_lt >> decide_tac) >>
      gvs[]) >> simp[])
  >> simp[] >>
  qspecl_then [`MAP (\i. (k+n2w i,ws i)) (COUNT_LIST n)`,
    `q`, `st`] mp_tac place_store_updates_miss >>
  simp[FOLDL_MAP] >> impl_tac >- (
  simp[MEM_MAP, MEM_COUNT_LIST, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `j < n` >>
  `w2n (k+n2w j) = w2n k+j` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  gvs[]) >> simp[]
QED

Theorem normalized_copy_prefix_footprint:
  store_copy_normalize s t =
    store_copy_prefix (if tr then LocTransient else LocStorage) b k s n /\
  w2n k+n <= dimword (:256) ==>
  !q.
    (if tr then tload q t else sload q t) =
      (if w2n k <= w2n q /\ w2n q < w2n k+n
       then mload (w2n (b+n2w (w2n q-w2n k)*32w)) s
       else if tr then tload q s else sload q s) /\
    (if tr then sload q t else tload q t) =
      (if tr then sload q s else tload q s)
Proof
  strip_tac >> gen_tac >>
  `(!r. (if r then tload q t else sload q t) =
    (if r then tload q else sload q)
      (store_copy_prefix (if tr then LocTransient else LocStorage) b k s n))` by
    (gen_tac >> qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
     Cases_on `r` >>
     simp[store_copy_normalize_def, venom_state_component_equality] >>
     strip_tac >> gvs[sload_def, tload_def,
       contract_storage_def, contract_transient_def]) >>
  conj_tac
  >- (first_assum (qspec_then `tr` SUBST1_TAC) >>
      qspecl_then [`n`, `s`, `b`, `k`, `tr`] assume_tac
        place_store_prefix_backend >>
      Cases_on `tr` >> gvs[sload_def, tload_def, copy_prefix_lookup]) >>
  qspecl_then [`n`, `s`, `b`, `k`, `tr`] assume_tac
    place_store_prefix_state_patch >>
  Cases_on `tr` >>
  gvs[store_copy_normalize_def, venom_state_component_equality,
      sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

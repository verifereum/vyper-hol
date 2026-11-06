Theory placeDynStorageEffect
Ancestors
  placeDynStoragePath placeStoreCopyPath stmtSimStoreCopy storageDynPrefixLive compileEnv venomState
  list rich_list arithmetic words

Theorem place_store_prefix_append:
  !j i s b k loc.
    store_copy_prefix loc b k s (i+j) =
    store_copy_prefix loc (b+n2w i*32w) (k+n2w i)
      (store_copy_prefix loc b k s i) j
Proof
  Induct_on `j` >- simp[place_store_prefix_eqs] >>
  rpt gen_tac >>
  simp[ADD_CLAUSES, place_store_prefix_eqs, place_store_prefix_fields,
       mload_def, GSYM word_add_n2w, WORD_LEFT_ADD_DISTRIB,
       WORD_RIGHT_ADD_DISTRIB,
       WORD_ADD_ASSOC]
QED

Theorem place_dyn_prefix_flat:
  place_dyn_prefix loc b k ew (32*ew) s j =
  store_copy_prefix loc (b+32w) (k+1w) s (j*ew)
Proof
  Induct_on `j` >- simp[place_dyn_prefix_eqs, place_store_prefix_eqs] >>
  `SUC j * ew = j * ew + ew` by simp[MULT_CLAUSES, ADD_COMM] >>
  pure_once_asm_rewrite_tac [] >>
  pure_rewrite_tac [place_dyn_prefix_eqs, place_store_prefix_append] >>
  asm_rewrite_tac [word_mul_n2w] >>
  simp_tac bool_ss [AC MULT_ASSOC MULT_COMM]
QED

Theorem place_selected_store_commute:
  a <> b ==>
  (if loc = LocStorage then sstore else tstore) a x
    ((if loc = LocStorage then sstore else tstore) b y s) =
  (if loc = LocStorage then sstore else tstore) b y
    ((if loc = LocStorage then sstore else tstore) a x s)
Proof
  strip_tac >> Cases_on `loc = LocStorage` >>
  simp[tstore_def, sstore_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM,
       combinTheory.UPDATE_COMMUTES]
QED

Theorem place_store_prefix_header:
  !i s. (!h. h < i ==> a <> k + n2w h) ==>
  (if loc = LocStorage then sstore else tstore) a x
    (store_copy_prefix loc b k s i) =
  store_copy_prefix loc b k
    ((if loc = LocStorage then sstore else tstore) a x s) i
Proof
  Induct_on `i` >- simp[place_store_prefix_eqs] >>
  rpt strip_tac >>
  `a <> k + n2w i` by (first_x_assum irule >> simp[]) >>
  `!h. h < i ==> a <> k + n2w h` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!h. h < SUC i ==> _` irule >> decide_tac) >>
  first_x_assum (drule_then (qspec_then `s` assume_tac)) >>
  pure_rewrite_tac [place_store_prefix_eqs] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [place_selected_store_commute] >>
  simp[] >>
  Cases_on `loc = LocStorage` >> simp[mload_def, tstore_def]
QED

Theorem place_store_prefix_backend:
  !i s b k tr.
  (if tr then contract_transient else contract_storage)
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s i) =
  FOLDL (\t h. update_storage (k+n2w h)
          (mload (w2n (b+n2w h*32w)) s) t)
    ((if tr then contract_transient else contract_storage) s) (COUNT_LIST i)
Proof
  Induct_on `i` >- simp[place_store_prefix_eqs, COUNT_LIST_def] >>
  rpt gen_tac >>
  simp[place_store_prefix_eqs, COUNT_LIST_SNOC, FOLDL_SNOC] >>
  first_x_assum (qspecl_then [`s`, `b`, `k`, `tr`] assume_tac) >>
  Cases_on `tr` >>
  gvs[contract_transient_def, contract_storage_def, tstore_def, sstore_def,
       place_store_prefix_fields, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem place_store_prefix_backend_natural:
  !tr. w2n b + 32*i <= dimword (:256) ==>
  (if tr then contract_transient else contract_storage)
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s i) =
  FOLDL (\t h. update_storage (k+n2w h)
          (mem_word_at (32*h+w2n b) s.vs_memory) t)
    ((if tr then contract_transient else contract_storage) s) (COUNT_LIST i)
Proof
  gen_tac >> strip_tac >> rewrite_tac[place_store_prefix_backend] >>
  irule FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  rename1 `h < i` >>
  `w2n b + 32*h < dimword (:256)` by decide_tac >>
  `b+n2w h*32w = n2w (w2n b+32*h)` by
    (rewrite_tac[word_mul_n2w] >>
     pure_rewrite_tac[GSYM word_add_n2w, n2w_w2n] >>
     simp_tac bool_ss [MULT_COMM]) >>
  simp[mload_def, valueEncodingTheory.mem_word_at_def]
QED

Theorem place_dyn_prefix_header_flat:
  (!h. h < j*ew ==> k <> (k+1w)+n2w h) /\
  mload (w2n b) s = x ==>
  (if loc = LocStorage then sstore else tstore) k x
    (place_dyn_prefix loc b k ew (32*ew) s j) =
  store_copy_prefix loc b k s (1+j*ew)
Proof
  strip_tac >>
  pure_rewrite_tac[place_dyn_prefix_flat, place_store_prefix_append] >>
  drule place_store_prefix_header >>
  disch_then (qspecl_then [`x`, `loc`, `b+32w`, `s`] mp_tac) >>
  simp[place_store_prefix_eqs,
       SRULE [] (Q.SPEC `0` (CONJUNCT2 place_store_prefix_eqs)),
       WORD_MULT_CLAUSES, WORD_ADD_0]
QED

Theorem place_dyn_storage_flat:
  L <= cap /\ w2n k+1+cap*ew <= dimword (:256) /\
  w2n b+32*(1+cap*ew) <= dimword (:256) /\
  mem_word_at (w2n b) s.vs_memory = n2w L ==>
  (if tr then tstore else sstore) k (n2w (w2n (n2w L:bytes32)))
    (place_dyn_prefix (if tr then LocTransient else LocStorage)
      b k ew (32*ew) s (w2n (n2w L:bytes32))) =
  store_copy_prefix (if tr then LocTransient else LocStorage) b k s (1+L*ew)
Proof
  strip_tac >>
  `L*ew <= cap*ew` by simp[LE_MULT_RCANCEL] >>
  `w2n (n2w L:bytes32)*ew = L*ew` by
    (Cases_on `ew` >- simp[] >>
     `L <= L*SUC n` by simp[MULT_CLAUSES] >>
     `L < dimword (:256)` by decide_tac >> simp[]) >>
  `!h. h < w2n (n2w L:bytes32)*ew ==> k <> k+1w+n2w h` by
    (rpt gen_tac >> disch_tac >>
     `w2n k+1+h < dimword (:256)` by decide_tac >>
     `k+1w+n2w h = n2w (w2n k+1+h)` by
       (pure_rewrite_tac [GSYM word_add_n2w, n2w_w2n] >> REFL_TAC) >>
     `w2n (k+1w+n2w h) = w2n k+1+h` by simp[] >>
     `w2n k <> w2n (k+1w+n2w h)` by decide_tac >>
     metis_tac[]) >>
  `mload (w2n b) s = n2w (w2n (n2w L:bytes32))` by
    gvs[mload_def, valueEncodingTheory.mem_word_at_def] >>
  drule_all place_dyn_prefix_header_flat >>
  disch_then (qspec_then `(if tr then LocTransient else LocStorage)` mp_tac) >>
  Cases_on `tr` >> simp[]
QED

Theorem place_store_prefix_state_patch:
  !i s b k tr.
  store_copy_prefix (if tr then LocTransient else LocStorage) b k s i =
  (if tr then s with vs_transient :=
      (s.vs_call_ctx.cc_address =+
        contract_transient (store_copy_prefix LocTransient b k s i)) s.vs_transient
   else s with vs_accounts :=
      (s.vs_call_ctx.cc_address =+
       (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
         contract_storage (store_copy_prefix LocStorage b k s i))) s.vs_accounts)
Proof
  Induct_on `i`
  >- (rpt gen_tac >> Cases_on `tr` >>
      simp[place_store_prefix_eqs, contract_transient_def, contract_storage_def,
           vfmStateTheory.lookup_account_def, combinTheory.UPDATE_def, SF ETA_ss]) >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`s`, `b`, `k`, `tr`] assume_tac) >>
  Cases_on `tr` >> gvs[] >>
  once_rewrite_tac[place_store_prefix_eqs] >>
  simp[sstore_def, tstore_def, contract_transient_def, contract_storage_def,
       place_store_prefix_fields, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  qpat_assum `store_copy_prefix _ _ _ _ _ = _`
    (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
  once_asm_rewrite_tac [] >>
  simp[contract_transient_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem place_dyn_storage_effect:
  L <= cap /\ w2n k+1+cap*ew <= dimword (:256) /\
  w2n b+32*(1+cap*ew) <= dimword (:256) /\
  mem_word_at (w2n b) s.vs_memory = n2w L ==>
  (if tr then contract_transient else contract_storage)
    ((if tr then tstore else sstore) k (n2w (w2n (n2w L:bytes32)))
      (place_dyn_prefix (if tr then LocTransient else LocStorage)
        b k ew (32*ew) s (w2n (n2w L:bytes32)))) =
  FOLDL (\t i. update_storage (k+n2w i)
    (mem_word_at (w2n b+32*i) s.vs_memory) t)
    ((if tr then contract_transient else contract_storage) s)
    (COUNT_LIST (1+L*ew))
Proof
  strip_tac >>
  `L*ew <= cap*ew` by simp[LE_MULT_RCANCEL] >>
  drule_all place_dyn_storage_flat >>
  disch_then (qspec_then `tr` SUBST1_TAC) >>
  Cases_on `tr` >> simp[]
  >- (irule (SRULE [] (Q.SPEC `T` place_store_prefix_backend_natural)) >> decide_tac) >>
  irule (SRULE [] (Q.SPEC `F` place_store_prefix_backend_natural)) >> decide_tac
QED

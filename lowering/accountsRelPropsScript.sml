(*
 * Properties of accounts_rel (#665): the state_rel component that relates
 * every address's accounts and transient storage, with no source pending
 * deletions.  The running contract's storage and transient storage agree
 * only on their live bytes (#637); everything else is equal.
 *
 * TOP-LEVEL:
 *   state_rel_accounts      — state_rel gives the agreement of the
 *                             accounts and transient storage that the
 *                             success case of the external result relation
 *                             asks for
 *   accounts_rel_set_storage, accounts_rel_set_transient — a write of the
 *                             running contract's storage or transient
 *                             storage on both sides keeps accounts_rel
 *   accounts_rel_sstore, accounts_rel_tstore — their case for one SSTORE
 *                             or TSTORE
 *   accounts_rel_take_call_outcome, accounts_rel_adopt_call_outcome — the
 *                             call oracle keeps accounts_rel: taking an
 *                             outcome changes neither side's accounts, and
 *                             both sides adopt it with adopt_outcome
 *   accounts_rel_call_request — the oracle requests of the two sides
 *                             agree as request_agree says
 *   take_outcome_agree      — agreeing requests take agreeing outcomes
 *   storage_agree_update, transient_agree_update — the same write on both
 *                             sides keeps agreement
 *   dead_bytes_range, dead_bytes_frame — dead bytes lie in a value's own
 *                             slots and depend only on them
 *   declared_storage_region_read_live, storage_read_live_head,
 *   storage_read_live_field — reads of a declared region see live bytes
 *   storage_agree_read_head — agreeing storages read a live value alike
 *   storage_dead_update_in_region, storage_dead_update_word_region,
 *   storage_dead_update_struct_word_field, storage_dead_update_zero — a
 *                             write inside a region that keeps its dead
 *                             bytes (a one-slot region, a one-slot field
 *                             of a storage struct) keeps the dead set; a
 *                             zero write only shrinks it
 *   accounts_agree_lookup   — agreeing accounts have equal balances,
 *                             code and nonces
 *   storage_dead_cx_cong, agree_cx_cong — the dead set depends only on
 *                             the context's sources, layouts and target
 *
 * Helper:
 *   storage_agree_refl, accounts_agree_refl, transient_agree_refl,
 *   request_agree_refl      — each agreement is reflexive
 *   accounts_rel_storage_transient — storage_rel and transient_rel are
 *                             accounts_rel's case for the running contract
 *   accounts_rel_frame, accounts_rel_updates — accounts_rel reads only
 *                             the accounts, transient storage and pending
 *                             deletions
 *)

Theory accountsRelProps
Ancestors
  compileEnv vyperState vyperCallOutcome extCallOracle vyperStoragePlaceRegion
  venomState venomCallOracleDefs vfmExecution vfmState

(* ===== Reflexivity ===== *)

Theorem storage_agree_refl[simp]:
  !D st. storage_agree D st st
Proof
  simp[storage_agree_def]
QED

Theorem accounts_agree_refl[simp]:
  !cx a. accounts_agree cx a a
Proof
  simp[accounts_agree_def]
QED

Theorem transient_agree_refl[simp]:
  !cx t. transient_agree cx t t
Proof
  simp[transient_agree_def]
QED

Theorem request_agree_refl[simp]:
  !cx rq. request_agree cx rq rq
Proof
  simp[request_agree_def, call_request_component_equality]
QED

(* ===== The success-case effects ===== *)

Theorem state_rel_accounts:
  !func cenv cx es s.
    state_rel func cenv cx es s ==>
    accounts_agree cx es.accounts s.vs_accounts /\
    transient_agree cx es.tStorage s.vs_transient /\
    es.pending_deletions = []
Proof
  rw[state_rel_def, accounts_rel_def]
QED

Theorem accounts_rel_storage_transient:
  !cx es s.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target ==>
    storage_rel cx s.vs_call_ctx.cc_address es s /\
    transient_rel cx s.vs_call_ctx.cc_address es s
Proof
  rw[accounts_rel_def, storage_rel_def, transient_rel_def,
     accounts_agree_def, transient_agree_def, contract_storage_def,
     contract_transient_def, lookup_account_def]
QED

(* ===== Frames ===== *)

(* accounts_rel reads only the accounts, transient storage and pending
   deletions of the source and the accounts and transient storage of
   Venom. *)
Theorem accounts_rel_frame:
  !cx es es' s s'.
    es'.accounts = es.accounts /\ es'.tStorage = es.tStorage /\
    es'.pending_deletions = es.pending_deletions /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient ==>
    (accounts_rel cx es' s' <=> accounts_rel cx es s)
Proof
  simp[accounts_rel_def]
QED

Theorem accounts_rel_updates[simp]:
  (!cx es s x w. accounts_rel cx es (update_var x w s) <=>
                 accounts_rel cx es s) /\
  (!cx es s V. accounts_rel cx es (s with vs_vars := V) <=>
               accounts_rel cx es s) /\
  (!cx es s lbl. accounts_rel cx es (jump_to lbl s) <=>
                 accounts_rel cx es s) /\
  (!cx es s n. accounts_rel cx es (s with vs_inst_idx := n) <=>
               accounts_rel cx es s) /\
  (!cx es s sc. accounts_rel cx (es with scopes := sc) s <=>
                accounts_rel cx es s)
Proof
  simp[accounts_rel_def, update_var_def, jump_to_def]
QED

(* ===== Writes of the running contract's storage ===== *)

(* The source sets the storage of cx.txn.target to stor, and Venom that of
   the running contract, the same address, to stor', which agrees with stor
   on the bytes live in stor. *)
Theorem accounts_rel_set_storage:
  !cx stor stor' es es' s s'.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    set_storage_backend cx F stor es = (INL (), es') /\
    storage_agree (storage_dead cx F stor) stor stor' /\
    s'.vs_accounts =
      (cx.txn.target =+
         (lookup_account cx.txn.target s.vs_accounts with storage := stor'))
        s.vs_accounts /\
    s'.vs_transient = s.vs_transient ==>
    accounts_rel cx es' s'
Proof
  rpt strip_tac >>
  gvs[set_storage_backend_def, vyperStateTheory.bind_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
      vyperStateTheory.return_def, accounts_rel_def, update_account_def,
      accounts_agree_def, lookup_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rw[] >>
  qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem accounts_rel_set_transient:
  !cx stor stor' es es' s s'.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    set_storage_backend cx T stor es = (INL (), es') /\
    storage_agree (storage_dead cx T stor) stor stor' /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = (cx.txn.target =+ stor') s.vs_transient ==>
    accounts_rel cx es' s'
Proof
  rw[set_storage_backend_def, vyperStateTheory.update_transient_def,
     vyperStateTheory.return_def] >>
  gvs[accounts_rel_def, update_transient_storage_def, transient_agree_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rw[]
QED

(* Both sides write v at k: the bytes at k agree after it, and every other
   byte still agrees if the write kills no dead byte elsewhere. *)
Theorem storage_agree_update:
  !D D' k v st1 st2.
    storage_agree D st1 st2 /\
    (!j b. D j b /\ j <> w2n k ==> D' j b) ==>
    storage_agree D' (update_storage k v st1) (update_storage k v st2)
Proof
  rw[storage_agree_def, update_storage_def, lookup_storage_def,
     combinTheory.APPLY_UPDATE_THM] >>
  rename1 `k = k'` >> Cases_on `k = k'` >> simp[] >>
  first_x_assum irule >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`w2n k'`, `b`] mp_tac) >> simp[]
QED

Theorem transient_agree_update:
  !cx t1 t2 k v.
    transient_agree cx t1 t2 /\
    (!j b. storage_dead cx T (t1 cx.txn.target) j b /\ j <> w2n k ==>
           storage_dead cx T (update_storage k v (t1 cx.txn.target)) j b) ==>
    transient_agree cx
      ((cx.txn.target =+ update_storage k v (t1 cx.txn.target)) t1)
      ((cx.txn.target =+ update_storage k v (t2 cx.txn.target)) t2)
Proof
  rw[transient_agree_def, combinTheory.APPLY_UPDATE_THM] >>
  irule storage_agree_update >>
  qexists_tac `storage_dead cx T (t1 cx.txn.target)` >> simp[]
QED

(* One SSTORE of v at k, which the source makes to its own storage.  The
   write must not make live a byte dead elsewhere: the bytes at k agree
   after it, and the others agree as before. *)
Theorem accounts_rel_sstore:
  !cx k v es es' s st.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    st = (lookup_account cx.txn.target es.accounts).storage /\
    (!j b. storage_dead cx F st j b /\ j <> w2n k ==>
           storage_dead cx F (update_storage k v st) j b) /\
    set_storage_backend cx F (update_storage k v st) es = (INL (), es') ==>
    accounts_rel cx es' (sstore k v s)
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `update_storage k v st`,
               `update_storage k v (contract_storage s)`, `es`, `es'`, `s`,
               `sstore k v s`] mp_tac accounts_rel_set_storage >>
  impl_tac >- (
    simp[sstore_def, contract_storage_def] >>
    irule storage_agree_update >>
    qexists_tac `storage_dead cx F st` >>
    gvs[accounts_rel_def, accounts_agree_def, lookup_account_def]) >>
  simp[]
QED

Theorem accounts_rel_tstore:
  !cx k v es es' s st.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    st = es.tStorage cx.txn.target /\
    (!j b. storage_dead cx T st j b /\ j <> w2n k ==>
           storage_dead cx T (update_storage k v st) j b) /\
    set_storage_backend cx T (update_storage k v st) es = (INL (), es') ==>
    accounts_rel cx es' (tstore k v s)
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `update_storage k v st`,
               `update_storage k v (contract_transient s)`, `es`, `es'`, `s`,
               `tstore k v s`] mp_tac accounts_rel_set_transient >>
  impl_tac >- (
    simp[tstore_def, contract_transient_def] >>
    irule storage_agree_update >>
    qexists_tac `storage_dead cx T st` >>
    gvs[accounts_rel_def, transient_agree_def]) >>
  simp[]
QED

(* ===== The call oracle ===== *)

Theorem accounts_rel_take_call_outcome:
  !cx target calldata value_opt es es' res s.
    accounts_rel cx es s /\
    take_call_outcome target calldata value_opt es = (res, es') ==>
    accounts_rel cx es' s
Proof
  rpt strip_tac >> drule take_call_outcome_frame >> strip_tac >>
  pop_assum SUBST1_TAC >> fs[accounts_rel_def]
QED

(* Agreeing requests take outcomes that differ at most in the accounts and
   transient storage, which agree: an outcome from the list is the same
   for both, and one computed from the request carries its accounts and
   transient storage. *)
Theorem take_outcome_agree:
  !cx rq1 rq2 os o1 o2 r1 r2.
    request_agree cx rq1 rq2 /\
    take_outcome rq1 os = (o1, r1) /\ take_outcome rq2 os = (o2, r2) ==>
    r1 = r2 /\
    o1 with <| co_accounts := o2.co_accounts;
               co_tStorage := o2.co_tStorage |> = o2 /\
    accounts_agree cx o1.co_accounts o2.co_accounts /\
    transient_agree cx o1.co_tStorage o2.co_tStorage
Proof
  rw[request_agree_def] >>
  `rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data /\
   rq1.cr_value = rq2.cr_value` by
    (qpat_x_assum `_ = rq2` (SUBST1_TAC o SYM) >> simp[]) >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def,
      AllCaseEqs()] >>
  simp[call_outcome_component_equality]
QED

(* Venom adopts an outcome with adopt_outcome on its accounts, transient
   storage and logs (consume_call_outcome), as the source does; the two
   outcomes and requests agree as take_outcome_agree gives. *)
Theorem accounts_rel_adopt_call_outcome:
  !cx rq rq' outcome outcome' es es' s s' logs.
    accounts_rel cx es s /\ adopt_call_outcome rq outcome es = (INL (), es') /\
    rq'.cr_static = rq.cr_static /\
    outcome with <| co_accounts := outcome'.co_accounts;
                    co_tStorage := outcome'.co_tStorage |> = outcome' /\
    accounts_agree cx outcome.co_accounts outcome'.co_accounts /\
    transient_agree cx outcome.co_tStorage outcome'.co_tStorage /\
    s'.vs_accounts =
      FST (adopt_outcome rq' outcome' (s.vs_accounts, s.vs_transient, logs)) /\
    s'.vs_transient =
      FST (SND (adopt_outcome rq' outcome'
                  (s.vs_accounts, s.vs_transient, logs))) ==>
    accounts_rel cx es' s'
Proof
  rw[adopt_call_outcome_equation] >>
  `outcome'.co_success = outcome.co_success` by
    (qpat_x_assum `_ = outcome'` (SUBST1_TAC o SYM) >> simp[]) >>
  gvs[accounts_rel_def, adopt_outcome_def] >>
  rw[] >> gvs[]
QED

Theorem accounts_rel_call_request:
  !cx es s target calldata value_opt.
    accounts_rel cx es s ==>
    accounts_agree cx
      (call_outcome_request target calldata value_opt es).cr_accounts
      s.vs_accounts /\
    transient_agree cx
      (call_outcome_request target calldata value_opt es).cr_tStorage
      s.vs_transient
Proof
  rw[accounts_rel_def, call_outcome_request_def]
QED

(* ===== Dead bytes ===== *)

(* A dead byte of a value lies in the value's slots past its first. *)
Theorem dead_bytes_range:
  (!st base tv j b.
     dead_bytes st base tv j b ==>
     base < j /\ j < base + type_slot_size tv /\ b < 32) /\
  (!st base tvs j b.
     dead_bytes_list st base tvs j b ==>
     base < j /\ j < base + type_slot_size_list tvs /\ b < 32) /\
  (!st base fs j b.
     dead_bytes_fields st base fs j b ==>
     base < j /\ j < base + type_slot_size_fields fs /\ b < 32)
Proof
  ho_match_mp_tac dead_bytes_ind >>
  rw[dead_bytes_def, dyn_bytes_dead_def, vyperValueTheory.type_slot_size_def] >>
  rpt (qpat_x_assum `if _ then _ else _` mp_tac >> IF_CASES_TAC >>
       strip_tac) >>
  rpt (first_x_assum drule_all >> strip_tac) >>
  rpt (qpat_x_assum `i < n`
         (strip_assume_tac o MATCH_MP arithmeticTheory.LESS_ADD_1)) >>
  gvs[arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.LEFT_ADD_DISTRIB]
QED

Theorem array_element_slot_bound[local]:
  !i n s base. i < n ==> base + i * s + s <= base + n * s
Proof
  rpt strip_tac >>
  drule arithmeticTheory.LESS_ADD_1 >> strip_tac >>
  simp[arithmeticTheory.RIGHT_ADD_DISTRIB,
       arithmeticTheory.LEFT_ADD_DISTRIB]
QED

(* Which bytes of a value are dead depends only on its own slots. *)
Theorem dead_bytes_frame:
  (!st base tv j b st'.
     (!i. base <= i /\ i < base + type_slot_size tv ==>
          lookup_storage (n2w i) st' = lookup_storage (n2w i) st) ==>
     (dead_bytes st' base tv j b <=> dead_bytes st base tv j b)) /\
  (!st base tvs j b st'.
     (!i. base <= i /\ i < base + type_slot_size_list tvs ==>
          lookup_storage (n2w i) st' = lookup_storage (n2w i) st) ==>
     (dead_bytes_list st' base tvs j b <=> dead_bytes_list st base tvs j b)) /\
  (!st base fs j b st'.
     (!i. base <= i /\ i < base + type_slot_size_fields fs ==>
          lookup_storage (n2w i) st' = lookup_storage (n2w i) st) ==>
     (dead_bytes_fields st' base fs j b <=> dead_bytes_fields st base fs j b))
Proof
  ho_match_mp_tac dead_bytes_ind >>
  rw[dead_bytes_def, dyn_bytes_dead_def, vyperValueTheory.type_slot_size_def] >>
  rename1 `!i. bs <= i /\ i < _ ==>
                lookup_storage (n2w i) st' = lookup_storage (n2w i) st`
  >- (`!i. i < n ==>
          (dead_bytes st' (bs + i * type_slot_size tv) tv j b <=>
           dead_bytes st (bs + i * type_slot_size tv) tv j b)` by
        (rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
         qpat_x_assum `!i. bs <= i /\ _ ==> _` irule >>
         qpat_x_assum `i < n` (mp_tac o MATCH_MP array_element_slot_bound) >>
         disch_then (qspecl_then [`type_slot_size tv`, `bs`] mp_tac) >>
         decide_tac) >>
      metis_tac[]) >>
  `!i. i < n /\ i < w2n (lookup_storage (n2w bs) st) ==>
       (dead_bytes st' (bs + (i * type_slot_size tv + 1)) tv j b <=>
        dead_bytes st (bs + (i * type_slot_size tv + 1)) tv j b)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `i < n` (mp_tac o MATCH_MP array_element_slot_bound) >>
     disch_then (qspecl_then [`type_slot_size tv`, `bs`] mp_tac) >>
     decide_tac) >>
  metis_tac[]
QED

(* A declared region is read live. *)
Theorem declared_storage_region_read_live:
  !cx mid n subs tr w tv st.
    declared_storage_region cx mid n subs = SOME (tr, w, tv) ==>
    storage_read_live cx tr st w tv
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac [storage_read_live_def, storage_dead_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `dead_bytes st (w2n slot) tv' j b` >>
  Cases_on `(slot, tv') = (w, tv)`
  >- gvs[] >>
  qpat_x_assum `!mid'' n'' subs'' slot'' tv''. _`
    (qspecl_then [`mid`, `n`, `subs`, `w`, `tv`] mp_tac) >>
  simp[vyperStorageFrameTheory.ranges_disjoint_def] >>
  drule (cj 1 dead_bytes_range) >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

(* A live read's first slot holds no dead byte. *)
Theorem storage_read_live_head:
  !cx tr st w tv b.
    storage_read_live cx tr st w tv /\ 0 < type_slot_size tv ==>
    ~storage_dead cx tr st (w2n w) b
Proof
  rw[storage_read_live_def] >> strip_tac >> first_x_assum drule >>
  strip_tac >> gvs[] >> drule (cj 1 dead_bytes_range) >> simp[]
QED

(* Words whose bytes agree are equal. *)
Theorem word_to_bytes_EL_eq:
  !(x:bytes32) y.
    (!b. b < 32 ==> EL b (word_to_bytes x T) = EL b (word_to_bytes y T)) ==>
    x = y
Proof
  rpt strip_tac >>
  `word_to_bytes x T = word_to_bytes y T` by
    (irule listTheory.LIST_EQ >>
     simp[byteTheory.LENGTH_word_to_bytes, fcpTheory.index_bit0,
          fcpTheory.index_one, fcpTheory.finite_bit0, fcpTheory.finite_one]) >>
  metis_tac[vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

(* Storage that agrees up to dead bytes holds the same word at the first
   slot of a live read. *)
Theorem storage_agree_read_head:
  !cx tr st st' w tv.
    storage_agree (storage_dead cx tr st) st st' /\
    storage_read_live cx tr st w tv /\ 0 < type_slot_size tv ==>
    lookup_storage w st' = lookup_storage w st
Proof
  rw[storage_agree_def] >> irule word_to_bytes_EL_eq >> rpt strip_tac >>
  drule_all storage_read_live_head >> metis_tac[]
QED

Theorem disjoint_word_update_lookup[local]:
  !base sz (k:bytes32) v st.
    ranges_disjoint base sz (w2n k) 1 ==>
    !i. base <= i /\ i < base + sz ==>
      lookup_storage (n2w i) (update_storage k v st) =
      lookup_storage (n2w i) st
Proof
  rpt gen_tac >>
  simp[vyperStorageFrameTheory.ranges_disjoint_def] >>
  rpt strip_tac >>
  `i < dimword (:256) /\ i <> w2n k` by decide_tac >>
  `(n2w i:bytes32) <> k` by
    (disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     asm_simp_tac pure_ss [wordsTheory.w2n_n2w,
                          arithmeticTheory.LESS_MOD] >> simp[]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem update_storage_lookup_other[local]:
  !(k:bytes32) u st i.
    i < dimword (:256) /\ i <> w2n k ==>
    lookup_storage (n2w i) (update_storage k u st) = lookup_storage (n2w i) st
Proof
  rpt strip_tac >>
  `(n2w i:bytes32) <> k` by
    (disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     asm_simp_tac pure_ss [wordsTheory.w2n_n2w,
                          arithmeticTheory.LESS_MOD] >> simp[]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem ranges_disjoint_within[local]:
  !a sa b sb c sc.
    ranges_disjoint a sa b sb /\ b <= c /\ c + sc <= b + sb ==>
    ranges_disjoint a sa c sc
Proof
  rw[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac
QED

(* A write to slot k leaves the dead bytes where they were if k lies in a
   declared region whose own dead bytes the write leaves alone: no other
   region with dead bytes overlaps that one.  Both conditions matter only
   when the region fits the slot space; otherwise no region has dead
   bytes. *)
Theorem storage_dead_update_in_region:
  !cx mid n subs tr k0 tv0 k u st.
    declared_storage_region cx mid n subs = SOME (tr, k0, tv0) /\
    (w2n k0 + type_slot_size tv0 <= dimword (:256) ==>
     w2n k0 <= w2n k /\ w2n k < w2n k0 + type_slot_size tv0 /\
     !j b. dead_bytes (update_storage k u st) (w2n k0) tv0 j b <=>
           dead_bytes st (w2n k0) tv0 j b) ==>
    storage_dead cx tr (update_storage k u st) = storage_dead cx tr st
Proof
  rpt gen_tac >> strip_tac >>
  simp[FUN_EQ_THM] >> map_every qx_gen_tac [`j`, `b`] >>
  pure_rewrite_tac [storage_dead_def] >> eq_tac >> strip_tac >>
  (rename1 `dead_bytes _ (w2n slot) tv' j b` >>
   `w2n k0 + type_slot_size tv0 <= dimword (:256)` by
     (Cases_on `(slot, tv') = (k0, tv0)` >- gvs[] >>
      qpat_x_assum `!mid'' n'' subs'' slot'' tv''. _`
        (qspecl_then [`mid`, `n`, `subs`, `k0`, `tv0`] mp_tac) >>
      simp[vyperStorageFrameTheory.ranges_disjoint_def]) >>
   qpat_x_assum `_ ==> _` drule >> strip_tac >>
   qexistsl_tac [`mid'`, `n'`, `subs'`, `slot`, `tv'`] >>
   rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
   Cases_on `(slot, tv') = (k0, tv0)` >- gvs[] >>
   `ranges_disjoint (w2n slot) (type_slot_size tv') (w2n k) 1` by
     (irule ranges_disjoint_within >>
      qexistsl_tac [`w2n k0`, `type_slot_size tv0`] >> simp[] >>
      qpat_x_assum `!mid'' n'' subs'' slot'' tv''. _`
        (qspecl_then [`mid`, `n`, `subs`, `k0`, `tv0`] mp_tac) >>
      simp[]) >>
   `(dead_bytes (update_storage k u st) (w2n slot) tv' j b <=>
     dead_bytes st (w2n slot) tv' j b)` by
     (irule (cj 1 dead_bytes_frame) >>
      rpt strip_tac >> irule disjoint_word_update_lookup >>
      qexistsl_tac [`w2n slot`, `type_slot_size tv'`] >> simp[]) >>
   gvs[])
QED

(* A write to a one-slot declared region leaves the dead bytes where they
   were: a one-slot value has none. *)
Theorem storage_dead_update_word_region:
  !cx mid n subs tr k tv v st.
    declared_storage_region cx mid n subs = SOME (tr, k, tv) /\
    type_slot_size tv = 1 ==>
    storage_dead cx tr (update_storage k v st) = storage_dead cx tr st
Proof
  rpt strip_tac >> irule storage_dead_update_in_region >>
  qexistsl_tac [`k`, `mid`, `n`, `subs`, `tv`] >> simp[] >>
  rpt strip_tac >> eq_tac >> strip_tac >>
  drule (cj 1 dead_bytes_range) >> simp[]
QED

(* A write to a one-slot field of a struct leaves the struct's dead bytes
   where they were: the field has none, and the other fields' slots are
   not written. *)
Theorem dead_bytes_fields_update_word[local]:
  !fs fld off ftv bs k u st j b.
    struct_field_slot fs fld = SOME (off, ftv) /\ type_slot_size ftv = 1 /\
    bs + type_slot_size_fields fs <= dimword (:256) /\
    w2n k = bs + off ==>
    (dead_bytes_fields (update_storage k u st) bs fs j b <=>
     dead_bytes_fields st bs fs j b)
Proof
  Induct_on `fs` >- simp[struct_field_slot_def] >>
  Cases >> rpt gen_tac >> rename1 `(fid, fty) :: fs` >>
  simp[struct_field_slot_def, vyperValueTheory.type_slot_size_def] >>
  strip_tac >> simp[dead_bytes_def] >>
  Cases_on `fid = fld` >> gvs[]
  >- (`~dead_bytes (update_storage k u st) (w2n k) ftv j b /\
       ~dead_bytes st (w2n k) ftv j b` by
        (rpt strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]) >>
      simp[] >> irule (cj 3 dead_bytes_frame) >> rpt strip_tac >>
      irule update_storage_lookup_other >> decide_tac) >>
  rename1 `struct_field_slot fs fld = SOME z` >> Cases_on `z` >> gvs[] >>
  rename1 `struct_field_slot fs fld = SOME (off, ftv)` >>
  `dead_bytes (update_storage k u st) bs fty j b <=>
   dead_bytes st bs fty j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     irule update_storage_lookup_other >> decide_tac) >>
  simp[] >> AP_TERM_TAC >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`fld`, `ftv`] >> simp[]
QED

(* A write to a one-slot field of a storage struct leaves the dead bytes
   where they were. *)
Theorem storage_dead_update_struct_word_field:
  !cx mid n tr k fs fld off ftv u st.
    declared_storage_region cx mid n [] = SOME (tr, k, StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\ type_slot_size ftv = 1 ==>
    storage_dead cx tr (update_storage (k + n2w off) u st) =
    storage_dead cx tr st
Proof
  rpt strip_tac >> irule storage_dead_update_in_region >>
  qexistsl_tac [`k`, `mid`, `n`, `[]`, `StructTV fs`] >> simp[] >>
  strip_tac >>
  drule struct_field_slot_end_bound >> strip_tac >>
  `w2n k + off < dimword (:256)` by
    (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (k + n2w off) = w2n k + off` by
    (Cases_on `k` >> fs[wordsTheory.word_add_n2w]) >>
  fs[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac >> irule dead_bytes_fields_update_word >>
  conj_tac >- simp[] >> qexistsl_tac [`fld`, `ftv`, `off`] >> simp[]
QED

(* Agreeing accounts differ at most in the running contract's storage. *)
Theorem accounts_agree_lookup:
  !cx a1 a2 addr.
    accounts_agree cx a1 a2 ==>
    (lookup_account addr a2).balance = (lookup_account addr a1).balance /\
    (lookup_account addr a2).code = (lookup_account addr a1).code /\
    (lookup_account addr a2).nonce = (lookup_account addr a1).nonce
Proof
  rw[accounts_agree_def, lookup_account_def] >>
  Cases_on `addr = cx.txn.target` >> gvs[] >>
  qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem dyn_bytes_dead_update_zero[local]:
  !st base max j b k.
    dyn_bytes_dead st base max j b ==>
    dyn_bytes_dead (update_storage k 0w st) base max j b
Proof
  rpt gen_tac >>
  rename1 `dyn_bytes_dead st start max j b` >>
  Cases_on `k = n2w start` >>
  simp[dyn_bytes_dead_def, lookup_storage_def, update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem dead_bytes_update_zero[local]:
  (!st base tv j b. dead_bytes st base tv j b ==>
     !k. dead_bytes (update_storage k 0w st) base tv j b) /\
  (!st base tvs j b. dead_bytes_list st base tvs j b ==>
     !k. dead_bytes_list (update_storage k 0w st) base tvs j b) /\
  (!st base fs j b. dead_bytes_fields st base fs j b ==>
     !k. dead_bytes_fields (update_storage k 0w st) base fs j b)
Proof
  ho_match_mp_tac dead_bytes_ind >>
  rw[dead_bytes_def]
  >- metis_tac[dyn_bytes_dead_update_zero]
  >- metis_tac[dyn_bytes_dead_update_zero]
  >- (qexists_tac `i` >> simp[])
  >- (qexists_tac `i` >> simp[] >>
      rename1 `lookup_storage (n2w start) st` >>
      Cases_on `k = n2w start`
      >- (gvs[lookup_storage_def, update_storage_def,
              combinTheory.APPLY_UPDATE_THM] >>
          qpat_x_assum `if _ then _ else _` mp_tac >>
          IF_CASES_TAC >> simp[] >> strip_tac >>
          drule (cj 1 dead_bytes_range) >>
          simp[arithmeticTheory.LEFT_ADD_DISTRIB,
               arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
      qpat_x_assum `if _ then _ else _` mp_tac >>
      IF_CASES_TAC >> strip_tac >>
      gvs[lookup_storage_def, update_storage_def,
          combinTheory.APPLY_UPDATE_THM])
  >> metis_tac[]
QED

(* Writing a zero word kills no dead byte: a zero length leaves at least as
   many bytes dead as any other. *)
Theorem storage_dead_update_zero:
  !cx tr st k j b.
    storage_dead cx tr st j b ==>
    storage_dead cx tr (update_storage k 0w st) j b
Proof
  rw[storage_dead_def] >>
  qexistsl_tac [`mid`, `n`, `subs`, `slot`, `tv`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (cj 1 dead_bytes_update_zero) >> simp[]
QED

(* ===== The context ===== *)

(* The dead bytes depend on the context only through its sources, layouts
   and running contract. *)
Theorem storage_dead_cx_cong:
  !cx cx'.
    cx'.sources = cx.sources /\ cx'.layouts = cx.layouts /\
    cx'.txn.target = cx.txn.target ==>
    storage_dead cx' = storage_dead cx
Proof
  rw[FUN_EQ_THM, storage_dead_def,
     vyperStorageLayoutSafetyTheory.declared_storage_region_def,
     vyperContextTheory.get_module_code_def,
     vyperStateTheory.lookup_var_slot_from_layout_def,
     vyperContextTheory.get_tenv_def]
QED

Theorem agree_cx_cong:
  !cx cx'.
    cx'.sources = cx.sources /\ cx'.layouts = cx.layouts /\
    cx'.txn.target = cx.txn.target ==>
    accounts_agree cx' = accounts_agree cx /\
    transient_agree cx' = transient_agree cx /\
    request_agree cx' = request_agree cx
Proof
  rpt strip_tac >> drule storage_dead_cx_cong >> strip_tac >>
  simp[FUN_EQ_THM, accounts_agree_def, transient_agree_def,
       request_agree_def]
QED

(* A field of a value read live is read live. *)
Theorem dead_bytes_fields_selected[local]:
  !fs id foff ftv st base j b.
    struct_field_slot fs id = SOME (foff,ftv) /\
    dead_bytes_fields st base fs j b /\
    base + foff <= j /\ j < base + foff + type_slot_size ftv ==>
    dead_bytes st (base + foff) ftv j b
Proof
  Induct_on `fs` >- simp[struct_field_slot_def] >>
  Cases >> rpt gen_tac >> rename1 `(fid, fty) :: fs` >>
  simp[struct_field_slot_def] >>
  Cases_on `fid = id`
  >- (rpt strip_tac >> gvs[Once dead_bytes_def] >>
      drule (cj 3 dead_bytes_range) >> simp[]) >>
  Cases_on `struct_field_slot fs id` >> simp[] >>
  rename1 `struct_field_slot fs id = SOME fsl` >> Cases_on `fsl` >>
  rename1 `struct_field_slot fs id = SOME (off, _)` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `dead_bytes_fields st bs ((fid, fty) :: fs) j b` >>
  qpat_x_assum `dead_bytes_fields _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac
  >- (drule (cj 1 dead_bytes_range) >> simp[]) >>
  `bs + type_slot_size fty + off = bs + (off + type_slot_size fty)`
    by decide_tac >>
  first_x_assum drule >>
  disch_then (qspecl_then [`st`, `bs + type_slot_size fty`, `j`, `b`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

Theorem storage_read_live_field:
  !cx tr st w fs id foff ftv.
    storage_read_live cx tr st w (StructTV fs) /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    storage_read_live cx tr st (w + n2w foff) ftv
Proof
  rpt gen_tac >> strip_tac >>
  drule struct_field_slot_end_bound >> strip_tac >>
  Cases_on `type_slot_size ftv = 0`
  >- (simp[storage_read_live_def] >>
      rpt strip_tac >> qspec_then `w + n2w foff` mp_tac wordsTheory.w2n_lt >>
      decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + foff < dimword (:256)` by decide_tac >>
  `w2n (w + n2w foff) = w2n w + foff` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes_fields st (w2n w) fs j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  drule dead_bytes_fields_selected >>
  disch_then (qspecl_then [`st`, `w2n w`, `j`, `b`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

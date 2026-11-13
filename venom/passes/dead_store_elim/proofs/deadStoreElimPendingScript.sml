Theory deadStoreElimPending
Ancestors
  deadStoreElimMemory deadStoreElimLocations deadStoreElimLiveness
  deadStoreElimDefs deadStoreElimEquiv venomState venomExecSemantics
  memLocDefs memAliasDefs basePtrDefs finite_map words list rich_list combin arithmetic vfmState deadStoreElimFrame
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Definition dse_pending_keys_def:
  dse_pending_keys (P : (mem_loc # (num # num)) list) =
    MAP (\(loc,(a,n)). (n2w a : bytes32)) P
End

Definition dse_key_normalize_def:
  (dse_key_normalize [] m = m) /\
  (dse_key_normalize (k::ks) m =
    update_storage k 0w (dse_key_normalize ks m))
End

Definition dse_accounts_normalize_def:
  dse_accounts_normalize c ks A =
    (c =+ ((A c) with storage := dse_key_normalize ks (A c).storage)) A
End

Definition dse_transient_normalize_def:
  dse_transient_normalize c ks ts =
    (c =+ dse_key_normalize ks (ts c)) ts
End

Definition key_ok_def:
  key_ok (P : (mem_loc # (num # num)) list) <=>
    EVERY (\(loc,(a,n)). n = 1 /\ a < dimword (:256)) P
End

Definition dse_pending_space_def:
  dse_pending_space sp P s t <=>
    dse_equiv sp s t /\
    (sp = AddrSp_Memory ==> dse_pending_memory (MAP SND P) s t) /\
    (sp = AddrSp_Storage ==>
      dse_accounts_normalize s.vs_call_ctx.cc_address (dse_pending_keys P) s.vs_accounts =
      dse_accounts_normalize t.vs_call_ctx.cc_address (dse_pending_keys P) t.vs_accounts) /\
    (sp = AddrSp_Transient ==>
      dse_transient_normalize s.vs_call_ctx.cc_address (dse_pending_keys P) s.vs_transient =
      dse_transient_normalize t.vs_call_ctx.cc_address (dse_pending_keys P) t.vs_transient)
End

Definition dse_pending_at_def:
  dse_pending_at cfg bp sp fn bb idx P s <=>
    EVERY (\(loc,(a,n)). ml_is_fixed loc /\ loc.ml_size = SOME n /\
      0 < n /\ dse_region_matches loc s a n /\
      dse_suffix_dead cfg FEMPTY bp loc sp fn bb idx) P /\
    ((sp = AddrSp_Storage \/ sp = AddrSp_Transient) ==> key_ok P)
End

Theorem dse_key_normalize_nil[simp]:
  dse_key_normalize [] m = m
Proof
  simp[dse_key_normalize_def]
QED

Theorem dse_key_normalize_apply:
  !ks m k. dse_key_normalize ks m k = if MEM k ks then 0w else m k
Proof
  Induct >> simp[dse_key_normalize_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `h = k` >> simp[]
QED

Theorem dse_key_normalize_update:
  dse_key_normalize ks (update_storage k v m) =
    if MEM k ks then dse_key_normalize ks m
    else update_storage k v (dse_key_normalize ks m)
Proof
  simp[FUN_EQ_THM, dse_key_normalize_apply, update_storage_def,
       APPLY_UPDATE_THM] >>
  Cases_on `MEM k ks` >> simp[] >>
  gen_tac >> Cases_on `k = x` >>
  gvs[APPLY_UPDATE_THM, dse_key_normalize_apply]
QED

Theorem dse_key_normalize_overwrite:
  dse_key_normalize ks m = dse_key_normalize ks q ==>
  dse_key_normalize (FILTER (\j. j <> k) ks) (update_storage k v m) =
  dse_key_normalize (FILTER (\j. j <> k) ks) (update_storage k v q)
Proof
  simp[FUN_EQ_THM, dse_key_normalize_apply, MEM_FILTER,
       update_storage_def, APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `k = x` >> simp[] >>
  Cases_on `MEM x ks` >> simp[] >> metis_tac[]
QED

Theorem dse_accounts_normalize_nil[simp]:
  dse_accounts_normalize c [] A = A
Proof
  simp[dse_accounts_normalize_def, FUN_EQ_THM, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `c = x` >> simp[]
QED

Theorem dse_transient_normalize_nil[simp]:
  dse_transient_normalize c [] ts = ts
Proof
  simp[dse_transient_normalize_def, FUN_EQ_THM, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `c = x` >> simp[]
QED

Theorem dse_accounts_normalize_other:
  d <> c ==> dse_accounts_normalize c ks A d = A d
Proof
  simp[dse_accounts_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_transient_normalize_other:
  d <> c ==> dse_transient_normalize c ks ts d = ts d
Proof
  simp[dse_transient_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_accounts_normalize_storage[simp]:
  (dse_accounts_normalize c ks A c).storage = dse_key_normalize ks (A c).storage
Proof
  simp[dse_accounts_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_accounts_normalize_nonce[simp]:
  (dse_accounts_normalize c ks A c).nonce = (A c).nonce
Proof
  simp[dse_accounts_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_accounts_normalize_balance[simp]:
  (dse_accounts_normalize c ks A c).balance = (A c).balance
Proof
  simp[dse_accounts_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_accounts_normalize_code[simp]:
  (dse_accounts_normalize c ks A c).code = (A c).code
Proof
  simp[dse_accounts_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_pending_space_refl:
  dse_pending_space sp P s s
Proof
  simp[dse_pending_space_def, dse_equiv_refl, dse_pending_memory_refl]
QED

Theorem dse_pending_space_equiv:
  dse_pending_space sp P s t ==> dse_equiv sp s t
Proof
  simp[dse_pending_space_def]
QED

Theorem dse_pending_space_storage_empty:
  dse_pending_space AddrSp_Storage [] s t ==> s.vs_accounts = t.vs_accounts
Proof
  simp[dse_pending_space_def, dse_pending_keys_def]
QED

Theorem dse_pending_space_transient_empty:
  dse_pending_space AddrSp_Transient [] s t ==> s.vs_transient = t.vs_transient
Proof
  simp[dse_pending_space_def, dse_pending_keys_def]
QED

Theorem dse_pending_space_memory_empty:
  dse_pending_space AddrSp_Memory [] s t ==> s.vs_memory = t.vs_memory
Proof
  simp[dse_pending_space_def] >> metis_tac[dse_pending_memory_empty]
QED

Theorem key_ok_insert:
  key_ok P ==> key_ok ((loc,(w2n (k:bytes32),1))::P)
Proof
  simp[key_ok_def, w2n_lt]
QED

Theorem key_ok_filter:
  key_ok P ==> key_ok (FILTER f P)
Proof
  simp[key_ok_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem dse_pending_at_empty:
  dse_pending_at cfg bp sp fn bb idx [] s
Proof
  simp[dse_pending_at_def, key_ok_def]
QED

Theorem dse_equiv_call_ctx:
  dse_equiv sp s t ==> s.vs_call_ctx = t.vs_call_ctx
Proof
  simp[dse_equiv_def] >> rpt strip_tac >>
  qpat_x_assum `dse_frame _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >> simp[]
QED

Theorem dse_pending_space_sload:
  dse_pending_space AddrSp_Storage P s t /\ key_ok P /\
  (!loc a n. MEM (loc,(a,n)) P ==> k <> n2w a) ==>
  sload k s = sload k t
Proof
  rpt strip_tac >>
  `~MEM k (dse_pending_keys P)` by
    (simp[dse_pending_keys_def, MEM_MAP] >>
     rpt strip_tac >> PairCases_on `y` >> gvs[] >> metis_tac[]) >>
  gvs[dse_pending_space_def] >>
  qpat_x_assum `dse_accounts_normalize _ _ _ = _`
    (mp_tac o Q.AP_TERM `\A. (A s.vs_call_ctx.cc_address).storage k`) >>
  simp[dse_key_normalize_apply, sload_def, contract_storage_def,
       lookup_account_def, lookup_storage_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_equiv_call_ctx >> simp[]) >>
  simp[dse_key_normalize_apply]
QED

Theorem dse_pending_space_tload:
  dse_pending_space AddrSp_Transient P s t /\ key_ok P /\
  (!loc a n. MEM (loc,(a,n)) P ==> k <> n2w a) ==>
  tload k s = tload k t
Proof
  rpt strip_tac >>
  `~MEM k (dse_pending_keys P)` by
    (simp[dse_pending_keys_def, MEM_MAP] >>
     rpt strip_tac >> PairCases_on `y` >> gvs[] >> metis_tac[]) >>
  gvs[dse_pending_space_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_equiv_call_ctx >> simp[]) >>
  qpat_x_assum `dse_transient_normalize _ _ _ = _`
    (mp_tac o Q.AP_TERM `\ts. ts s.vs_call_ctx.cc_address k`) >>
  simp[dse_transient_normalize_def, APPLY_UPDATE_THM,
       dse_key_normalize_apply, tload_def, contract_transient_def,
       lookup_storage_def]
QED

Theorem dse_accounts_normalize_cons:
  dse_accounts_normalize c (k::ks) A =
  dse_accounts_normalize c [k] (dse_accounts_normalize c ks A)
Proof
  simp[dse_accounts_normalize_def, dse_key_normalize_def,
       FUN_EQ_THM, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `c = x` >> gvs[]
QED

Theorem dse_transient_normalize_cons:
  dse_transient_normalize c (k::ks) ts =
  dse_transient_normalize c [k] (dse_transient_normalize c ks ts)
Proof
  simp[dse_transient_normalize_def, dse_key_normalize_def,
       FUN_EQ_THM, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `c = x` >> gvs[]
QED

Theorem dse_accounts_normalize_update:
  MEM k ks ==>
  dse_accounts_normalize c ks
    ((c =+ ((A c) with storage := update_storage k v (A c).storage)) A) =
  dse_accounts_normalize c ks A
Proof
  strip_tac >>
  simp[dse_accounts_normalize_def, dse_key_normalize_update,
       FUN_EQ_THM, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `c = x` >> gvs[]
QED

Theorem dse_transient_normalize_update:
  MEM k ks ==>
  dse_transient_normalize c ks ((c =+ update_storage k v (ts c)) ts) =
  dse_transient_normalize c ks ts
Proof
  strip_tac >>
  simp[dse_transient_normalize_def, dse_key_normalize_update,
       FUN_EQ_THM, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `c = x` >> gvs[]
QED

Theorem dse_pending_space_sstore_insert:
  dse_pending_space AddrSp_Storage P s t /\ key_ok P ==>
  dse_pending_space AddrSp_Storage ((loc,(w2n k,1))::P) (sstore k v s) t
Proof
  simp[dse_pending_space_def, dse_pending_keys_def] >> rpt strip_tac
  >- (gvs[dse_equiv_def, lookup_var_def] >> simp[sstore_def, lookup_var_def]) >>
  simp[sstore_def, lookup_account_def, dse_accounts_normalize_update] >>
  drule dse_equiv_call_ctx >> strip_tac >>
  once_rewrite_tac[dse_accounts_normalize_cons] >> gvs[]
QED

Theorem dse_pending_space_tstore_insert:
  dse_pending_space AddrSp_Transient P s t /\ key_ok P ==>
  dse_pending_space AddrSp_Transient ((loc,(w2n k,1))::P) (tstore k v s) t
Proof
  simp[dse_pending_space_def, dse_pending_keys_def] >> rpt strip_tac
  >- (gvs[dse_equiv_def, lookup_var_def] >> simp[tstore_def, lookup_var_def]) >>
  simp[tstore_def, dse_transient_normalize_update] >>
  drule dse_equiv_call_ctx >> strip_tac >>
  once_rewrite_tac[dse_transient_normalize_cons] >> gvs[]
QED

Theorem dse_accounts_normalize_overwrite:
  dse_accounts_normalize c ks A = dse_accounts_normalize c ks B ==>
  dse_accounts_normalize c (FILTER (\j. j <> k) ks)
    ((c =+ ((A c) with storage := update_storage k v (A c).storage)) A) =
  dse_accounts_normalize c (FILTER (\j. j <> k) ks)
    ((c =+ ((B c) with storage := update_storage k v (B c).storage)) B)
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  qpat_x_assum `dse_accounts_normalize _ _ _ = _`
    (fn th => mp_tac (Q.AP_THM th `x`)) >>
  Cases_on `c = x`
  >- (gvs[dse_accounts_normalize_def, APPLY_UPDATE_THM,
          account_state_component_equality] >>
      metis_tac[dse_key_normalize_overwrite]) >>
  simp[dse_accounts_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_transient_normalize_overwrite:
  dse_transient_normalize c ks ts = dse_transient_normalize c ks us ==>
  dse_transient_normalize c (FILTER (\j. j <> k) ks)
    ((c =+ update_storage k v (ts c)) ts) =
  dse_transient_normalize c (FILTER (\j. j <> k) ks)
    ((c =+ update_storage k v (us c)) us)
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  qpat_x_assum `dse_transient_normalize _ _ _ = _`
    (fn th => mp_tac (Q.AP_THM th `x`)) >>
  Cases_on `c = x`
  >- (gvs[dse_transient_normalize_def, APPLY_UPDATE_THM] >>
      metis_tac[dse_key_normalize_overwrite]) >>
  simp[dse_transient_normalize_def, APPLY_UPDATE_THM]
QED

Theorem dse_pending_keys_filter:
  dse_pending_keys (FILTER (\(loc,(a,n)). n2w a <> k) P) =
  FILTER (\j. j <> k) (dse_pending_keys P)
Proof
  Induct_on `P` >- simp[dse_pending_keys_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[dse_pending_keys_def] >> Cases_on `(n2w h1:bytes32) = k` >>
  gvs[dse_pending_keys_def]
QED

Theorem dse_pending_space_sstore_overwrite:
  dse_pending_space AddrSp_Storage P s t /\ key_ok P ==>
  dse_pending_space AddrSp_Storage
    (FILTER (\(loc,(a,n)). n2w a <> k) P) (sstore k v s) (sstore k v t)
Proof
  simp[dse_pending_space_def] >> rpt strip_tac
  >- (gvs[dse_equiv_def, lookup_var_def] >> simp[sstore_def, lookup_var_def]) >>
  drule dse_equiv_call_ctx >> strip_tac >>
  simp[sstore_def, lookup_account_def, dse_pending_keys_filter] >>
  irule dse_accounts_normalize_overwrite >> gvs[]
QED

Theorem dse_pending_space_tstore_overwrite:
  dse_pending_space AddrSp_Transient P s t /\ key_ok P ==>
  dse_pending_space AddrSp_Transient
    (FILTER (\(loc,(a,n)). n2w a <> k) P) (tstore k v s) (tstore k v t)
Proof
  simp[dse_pending_space_def] >> rpt strip_tac
  >- (gvs[dse_equiv_def, lookup_var_def] >> simp[tstore_def, lookup_var_def]) >>
  drule dse_equiv_call_ctx >> strip_tac >>
  simp[tstore_def, dse_pending_keys_filter] >>
  irule dse_transient_normalize_overwrite >> gvs[]
QED

(* Fixed-state liveness boundaries for outstanding footprints. *)
Theorem dse_pending_at_member:
  dse_pending_at cfg bp sp fn bb idx P s /\ MEM (loc,(a,n)) P ==>
  ml_is_fixed loc /\ loc.ml_size = SOME n /\ 0 < n /\
  dse_region_matches loc s a n /\
  dse_suffix_dead cfg FEMPTY bp loc sp fn bb idx
Proof
  simp[dse_pending_at_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem dse_pending_at_no_read:
  dse_pending_at cfg bp sp fn bb idx P s /\ MEM (loc,(a,n)) P /\
  idx < LENGTH bb.bb_instructions ==>
  ~dse_inst_reads_alias FEMPTY bp sp loc (EL idx bb.bb_instructions)
Proof
  rpt strip_tac >> drule_all dse_pending_at_member >> strip_tac >>
  drule_all dse_suffix_dead_no_read >> simp[]
QED

Theorem dse_pending_at_step:
  dse_pending_at cfg bp sp fn bb idx P s /\
  (!loc a n. MEM (loc,(a,n)) P ==>
    ~dse_inst_clobbers bp sp loc (EL idx bb.bb_instructions)) ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s
Proof
  rewrite_tac[dse_pending_at_def] >> strip_tac >>
  reverse conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  simp[EVERY_MEM] >> qx_gen_tac `entry` >> strip_tac >>
  PairCases_on `entry` >> gvs[] >>
  qpat_x_assum `EVERY _ P` mp_tac >> simp[EVERY_MEM] >>
  disch_then drule >> simp[] >> strip_tac >>
  irule dse_suffix_dead_step >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem dse_pending_at_nonalias:
  dse_pending_at cfg bp sp fn bb idx P s /\ MEM (loc,(a,n)) P /\
  ~may_overlap loc readloc /\ allocas_non_overlapping s /\
  dse_region_matches readloc s r m ==>
  regions_disjoint (a,n) (r,m)
Proof
  rpt strip_tac >> drule_all dse_pending_at_member >> strip_tac >>
  irule dse_region_matches_nonalias >> metis_tac[]
QED

Theorem dse_pending_at_filter:
  dse_pending_at cfg bp sp fn bb idx P s ==>
  dse_pending_at cfg bp sp fn bb idx (FILTER pred P) s
Proof
  simp[dse_pending_at_def, key_ok_def, EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem dse_pending_at_allocas_extend:
  dse_pending_at cfg bp sp fn bb idx P s /\
  (!aid p. FLOOKUP s.vs_allocas aid = SOME p ==>
           FLOOKUP t.vs_allocas aid = SOME p) ==>
  dse_pending_at cfg bp sp fn bb idx P t
Proof
  rewrite_tac[dse_pending_at_def] >> strip_tac >>
  reverse conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  simp[EVERY_MEM] >> qx_gen_tac `entry` >> strip_tac >>
  PairCases_on `entry` >> gvs[] >>
  qpat_x_assum `EVERY _ P` mp_tac >> simp[EVERY_MEM] >>
  disch_then drule >> simp[] >> strip_tac >>
  irule dse_region_matches_allocas_extend >> metis_tac[]
QED

Theorem dse_pending_at_undefined_read:
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\
  bp_get_read_location bp (EL idx bb.bb_instructions) sp = ml_undefined ==>
  P = []
Proof
  strip_tac >> Cases_on `P` >- simp[] >>
  rename1 `entry::rest` >> PairCases_on `entry` >>
  `MEM (entry0,(entry1,entry2)) ((entry0,(entry1,entry2))::rest)` by simp[] >>
  drule_all dse_pending_at_no_read >>
  drule_all dse_pending_at_member >> strip_tac >>
  simp[dse_inst_reads_alias_def, ma_may_alias_def, ml_undefined_def,
       may_overlap_def]
QED

Theorem dse_pending_space_read_memory:
  dse_pending_space AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  allocas_non_overlapping s /\ dse_region_matches readloc s r m /\
  (!loc a n. MEM (loc,(a,n)) P ==> ~may_overlap loc readloc) ==>
  read_memory r m s = read_memory r m t
Proof
  strip_tac >> irule dse_pending_memory_read_memory >>
  qexists_tac `MAP SND P` >>
  simp[MEM_MAP, PULL_EXISTS] >>
  reverse conj_tac >- fs[dse_pending_space_def] >>
  qx_gen_tac `a` >> qx_gen_tac `n` >> qx_gen_tac `entry` >>
  PairCases_on `entry` >> simp[] >> strip_tac >> gvs[] >>
  irule dse_pending_at_nonalias >> metis_tac[]
QED

Theorem dse_pending_at_read_memory:
  dse_pending_space AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ allocas_non_overlapping s /\
  dse_region_matches
    (bp_get_read_location bp (EL idx bb.bb_instructions) AddrSp_Memory)
    s r m ==>
  read_memory r m s = read_memory r m t
Proof
  strip_tac >> irule dse_pending_space_read_memory >>
  rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> drule_all dse_pending_at_no_read >>
  simp[dse_inst_reads_alias_def, ma_may_alias_def] >>
  metis_tac[memLocPropsTheory.may_overlap_sym]
QED

(* Concrete overwrites may discharge more entries than static clobbering
   recognizes; only the forward coverage implication is needed. *)
Theorem dse_pending_at_overwrite_step:
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  (!loc b m. MEM (loc,(b,m)) P /\ dse_inst_clobbers bp sp loc inst ==>
    a <= b /\ b+m <= a+n) ==>
  dse_pending_at cfg bp sp fn bb (SUC idx)
    (FILTER (\(loc,(b,m)). ~(a <= b /\ b+m <= a+n)) P) s
Proof
  strip_tac >>
  `dse_pending_at cfg bp sp fn bb idx
    (FILTER (\(loc,(b,m)). ~(a <= b /\ b+m <= a+n)) P) s` by
    (irule dse_pending_at_filter >> simp[]) >>
  irule dse_pending_at_step >> simp[MEM_FILTER] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem dse_pending_at_cons:
  dse_pending_at cfg bp sp fn bb idx P s /\
  ml_is_fixed loc /\ loc.ml_size = SOME n /\ 0 < n /\
  dse_region_matches loc s a n /\
  dse_suffix_dead cfg FEMPTY bp loc sp fn bb idx /\
  ((sp = AddrSp_Storage \/ sp = AddrSp_Transient) ==>
    n = 1 /\ a < dimword (:256)) ==>
  dse_pending_at cfg bp sp fn bb idx ((loc,(a,n))::P) s
Proof
  simp[dse_pending_at_def, key_ok_def] >> metis_tac[]
QED

Theorem dse_pending_at_insert_overwrite_step:
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  (!loc b m. MEM (loc,(b,m)) P /\ dse_inst_clobbers bp sp loc inst ==>
    a <= b /\ b+m <= a+n) /\
  ml_is_fixed newloc /\ newloc.ml_size = SOME n /\ 0 < n /\
  dse_region_matches newloc s a n /\
  dse_suffix_dead cfg FEMPTY bp newloc sp fn bb (SUC idx) /\
  ((sp = AddrSp_Storage \/ sp = AddrSp_Transient) ==>
    n = 1 /\ a < dimword (:256)) ==>
  dse_pending_at cfg bp sp fn bb (SUC idx)
    ((newloc,(a,n))::
      FILTER (\(loc,(b,m)). ~(a <= b /\ b+m <= a+n)) P) s
Proof
  strip_tac >> irule dse_pending_at_cons >> simp[] >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  irule (SRULE [] dse_pending_at_overwrite_step) >> metis_tac[]
QED

Theorem dse_pending_at_clobber_covered:
  dse_pending_at cfg bp sp fn bb idx P s /\
  MEM (loc,(b,m)) P /\ dse_inst_clobbers bp sp loc inst /\
  dse_region_matches (bp_get_write_location bp inst sp) s a n /\
  (bp_get_write_location bp inst sp).ml_size = SOME n ==>
  a <= b /\ b+m <= a+n
Proof
  strip_tac >> drule_all dse_pending_at_member >> strip_tac >>
  `completely_contains (bp_get_write_location bp inst sp) loc` by
    fs[dse_inst_clobbers_def] >>
  drule_all dse_region_matches_contains >> simp[]
QED

Theorem dse_key_normalize_insert_filter:
  dse_key_normalize (k::FILTER (\j. j <> k) ks) m =
  dse_key_normalize (k::ks) m
Proof
  simp[FUN_EQ_THM, dse_key_normalize_apply, MEM_FILTER] >>
  gen_tac >> Cases_on `x = k` >> simp[]
QED

Theorem dse_accounts_normalize_insert_filter:
  dse_accounts_normalize c (k::FILTER (\j. j <> k) ks) A =
  dse_accounts_normalize c (k::ks) A
Proof
  simp[dse_accounts_normalize_def, dse_key_normalize_insert_filter]
QED

Theorem dse_transient_normalize_insert_filter:
  dse_transient_normalize c (k::FILTER (\j. j <> k) ks) ts =
  dse_transient_normalize c (k::ks) ts
Proof
  simp[dse_transient_normalize_def, dse_key_normalize_insert_filter]
QED

Theorem dse_pending_space_sstore_insert_cover:
  dse_pending_space AddrSp_Storage P s t /\ key_ok P ==>
  dse_pending_space AddrSp_Storage
    ((loc,(w2n k,1))::FILTER (\(loc,(a,n)). n2w a <> k) P) (sstore k v s) t
Proof
  strip_tac >> drule_all dse_pending_space_sstore_insert >>
  disch_then (qspecl_then [`v`, `loc`, `k`] mp_tac) >>
  simp[dse_pending_space_def, dse_pending_keys_def,
       SRULE [dse_pending_keys_def] dse_pending_keys_filter,
       dse_accounts_normalize_insert_filter]
QED

Theorem dse_pending_space_tstore_insert_cover:
  dse_pending_space AddrSp_Transient P s t /\ key_ok P ==>
  dse_pending_space AddrSp_Transient
    ((loc,(w2n k,1))::FILTER (\(loc,(a,n)). n2w a <> k) P) (tstore k v s) t
Proof
  strip_tac >> drule_all dse_pending_space_tstore_insert >>
  disch_then (qspecl_then [`v`, `loc`, `k`] mp_tac) >>
  simp[dse_pending_space_def, dse_pending_keys_def,
       SRULE [dse_pending_keys_def] dse_pending_keys_filter,
       dse_transient_normalize_insert_filter]
QED

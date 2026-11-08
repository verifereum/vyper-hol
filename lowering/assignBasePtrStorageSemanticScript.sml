(* Semantic projections of the existing counted storage prefix model. *)
Theory assignBasePtrStorageSemantic
Ancestors assignBasePtrStorageLoop storageCopyLive assignBasePtrStorageFrame
  exprLoweringProps
  exprSimDefs exprSimProps loweringPosts compileEnv stmtSimStoreCopy valueEncodingProps stateFrame
  accountsRelProps vyperStorageFrame vyperStorageBackend vyperStorage venomState vfmState
  words arithmetic list rich_list combin

Theorem assign_base_store_backend_fold:
  !is k ws s tr.
    FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is =
    if tr then
      s with vs_transient :=
        (s.vs_call_ctx.cc_address =+
          FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
            (contract_transient s) is) s.vs_transient
    else
      s with vs_accounts :=
        (s.vs_call_ctx.cc_address =+
          (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
            FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
              (contract_storage s) is)) s.vs_accounts
Proof
  Induct >> rpt gen_tac >> Cases_on `tr` >>
  simp[FOLDL, sstore_def, tstore_def, contract_storage_def,
       contract_transient_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
QED

Theorem assign_base_store_fold_lookup:
  !is st addr f q w.
    (!i. MEM i is /\ addr i = q ==> f i = w) ==>
    lookup_storage q (FOLDL (\t i. update_storage (addr i) (f i) t) st is) =
    if MEM q (MAP addr is) then w else lookup_storage q st
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`update_storage (addr h) (f h) st`, `addr`, `f`, `q`, `w`] mp_tac) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem assign_base_store_fold_region:
  !k n q ws st.
    w2n k+n <= dimword (:256) ==>
    lookup_storage q
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        st (COUNT_LIST n)) =
    if w2n k <= w2n q /\ w2n q < w2n k+n then
      ws (w2n q-w2n k)
    else lookup_storage q st
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM i (COUNT_LIST n) /\ k+n2w i = q ==>
       ws i = ws (w2n q-w2n k)` by
    (simp[MEM_COUNT_LIST] >> rpt strip_tac >>
     `w2n k+i < dimword (:256)` by decide_tac >>
     `q = n2w (w2n k+i)` by simp[GSYM word_add_n2w] >>
     `w2n q = w2n k+i` by metis_tac[w2n_n2w, LESS_MOD] >>
     `w2n q-w2n k = i` by decide_tac >> simp[]) >>
  `MEM q (MAP (\i. k+n2w i) (COUNT_LIST n)) <=>
   w2n k <= w2n q /\ w2n q < w2n k+n` by
    (simp[MEM_MAP, MEM_COUNT_LIST] >> eq_tac
     >- (strip_tac >> rename1 `q = k+n2w y` >>
         `w2n k+y < dimword (:256)` by decide_tac >>
         `q = n2w (w2n k+y)` by simp[GSYM word_add_n2w] >>
         `w2n q = w2n k+y` by metis_tac[w2n_n2w, LESS_MOD] >> decide_tac) >>
     strip_tac >> qexists_tac `w2n q-w2n k` >>
     `w2n k+(w2n q-w2n k) = w2n q` by decide_tac >>
     conj_tac >-
       (qpat_x_assum `w2n k+_ = w2n q`
          (mp_tac o AP_TERM ``n2w:num -> bytes32``) >>
        pure_rewrite_tac[GSYM word_add_n2w, n2w_w2n] >> metis_tac[]) >> decide_tac) >>
  qpat_x_assum `MEM q _ <=> _` (fn th => rewrite_tac[GSYM th]) >>
  ho_match_mp_tac assign_base_store_fold_lookup >> simp[]
QED

Theorem assign_base_store_accounts_fold:
  !cx es s tr k ws is stor.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    accounts_rel cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  simp[assign_base_store_backend_fold] >> Cases_on `tr` >> gvs[]
  >- (irule accounts_rel_set_transient >>
      qexistsl_tac [`es`, `s`, `stor`] >>
      simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]) >>
  irule accounts_rel_set_storage >>
  qexistsl_tac [`es`, `s`, `stor`] >>
  simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem assign_base_store_state_fold:
  !ctx func cenv cx es s tr k ws is stor.
    stmt_state_rel ctx func cenv cx es s /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    stmt_state_rel ctx func cenv cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all assign_base_store_accounts_fold >> strip_tac >>
  qmatch_asmsub_abbrev_tac `accounts_rel cx es1 s1` >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`, assign_base_store_backend_fold] >>
     fs[stmt_state_rel_def, state_rel_def, set_storage_def,
        local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
        immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, assign_base_store_backend_fold,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, assign_base_store_backend_fold, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, assign_base_store_backend_fold]
QED

Theorem assign_base_store_initial_agree:
  !ctx func cenv cx es s tr.
    stmt_state_rel ctx func cenv cx es s ==>
    storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)
Proof
  rpt strip_tac >> Cases_on `tr` >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def,
     transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]
QED

Theorem assign_base_store_state_region:
  !ctx func cenv cx es s tr mid id subs k tv v writes off mem ws res es'.
    stmt_state_rel ctx func cenv cx es s /\
    declared_storage_region cx mid id subs = SOME (tr,k,tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (k,tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes k writes (get_storage cx es tr))
                (w2n k) tv (w2n k+i) b) ==>
         ws i = mem_word_at (off+32*i) mem) /\
    write_storage_slot cx tr k tv v es = (res,es') ==>
    res = INL () /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t)
        s (COUNT_LIST (type_slot_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `tr` assume_tac) assign_base_store_initial_agree >>
  drule_all storage_agree_copy_region >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[write_storage_slot_eq] >>
  irule assign_base_store_state_fold >> simp[]
QED

Theorem assign_base_store_frame_backend:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 n s tn ==>
  (if tr then contract_transient s else contract_storage s) =
  FOLDL (\t i. update_storage (k+n2w i)
    (mload (w2n (b+n2w i*32w)) s0) t)
    (if tr then contract_transient s0 else contract_storage s0) (COUNT_LIST n)
Proof
  simp[assign_base_store_frame_def, store_copy_prefix_def] >> strip_tac >>
  `(if (if tr then LocTransient else LocStorage) = LocStorage
    then sstore else tstore) = (if tr then tstore else sstore)` by
    (Cases_on `tr` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `s.vs_accounts = _` mp_tac >>
  qpat_x_assum `s.vs_transient = _` mp_tac >>
  simp[assign_base_store_backend_fold] >>
  Cases_on `tr` >>
  simp[contract_storage_def, contract_transient_def,
    lookup_account_def, APPLY_UPDATE_THM]
QED

Theorem assign_base_store_frame_lookup:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 n s tn /\ w2n k+n <= dimword (:256) ==>
  lookup_storage q (if tr then contract_transient s else contract_storage s) =
  if w2n k <= w2n q /\ w2n q < w2n k+n then
    mload (w2n (b+n2w (w2n q-w2n k)*32w)) s0
  else lookup_storage q (if tr then contract_transient s0 else contract_storage s0)
Proof
  strip_tac >> drule assign_base_store_frame_backend >>
  disch_then SUBST1_TAC >> ho_match_mp_tac assign_base_store_fold_region >> simp[]
QED

Theorem assign_base_store_frame_outside:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 n s tn /\ w2n k+n <= dimword (:256) /\
  x < dimword (:256) /\ ~(w2n k <= x /\ x < w2n k+n) ==>
  lookup_storage (n2w x) (if tr then contract_transient s else contract_storage s) =
  lookup_storage (n2w x) (if tr then contract_transient s0 else contract_storage s0)
Proof
  strip_tac >> drule_all assign_base_store_frame_lookup >>
  disch_then (qspec_then `n2w x` mp_tac) >>
  simp[w2n_n2w, LESS_MOD]
QED

Theorem assign_base_store_source_word:
  i < n /\ w2n (b:bytes32)+32*(n-1) < dimword (:256) ==>
  mload (w2n (b+n2w i*32w)) s0 =
  mem_word_at (w2n b+32*i) s0.vs_memory
Proof
  strip_tac >>
  `w2n b+32*i < dimword (:256)` by
    (`i <= n-1` by decide_tac >> decide_tac) >>
  `b+n2w i*32w = n2w (w2n b+32*i)` by
    (pure_rewrite_tac[GSYM word_add_n2w, GSYM word_mul_n2w, n2w_w2n] >>
     metis_tac[WORD_MULT_COMM]) >>
  simp[w2n_n2w, LESS_MOD, mem_word_at_eq_mload]
QED

Theorem assign_base_store_frame_live:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (type_slot_size tv) s tn /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s0.vs_memory /\
  encode_value tv v = SOME writes /\
  w2n k+type_slot_size tv <= dimword (:256) /\
  w2n b+32*(type_slot_size tv-1) < dimword (:256) /\
  w2n k <= x /\ x < w2n k+type_slot_size tv /\ c < 32 /\
  ~dead_bytes (apply_writes k writes st) (w2n k) tv x c ==>
  EL c (word_to_bytes
    (lookup_storage (n2w x) (if tr then contract_transient s else contract_storage s)) T) =
  EL c (word_to_bytes (lookup_storage (n2w x) (apply_writes k writes st)) T)
Proof
  strip_tac >>
  `x < dimword (:256) /\ x-w2n k < type_slot_size tv /\
   w2n k+(x-w2n k) = x` by decide_tac >>
  drule_all assign_base_store_frame_lookup >>
  disch_then (qspec_then `n2w x` mp_tac) >>
  simp[w2n_n2w, LESS_MOD] >> disch_then SUBST1_TAC >>
  `mload (w2n (b+n2w (x-w2n k)*32w)) s0 =
   mem_word_at (w2n b+32*(x-w2n k)) s0.vs_memory` by
    (irule assign_base_store_source_word >> qexists_tac `type_slot_size tv` >> simp[]) >>
  simp[] >> metis_tac[encode_value_memory_live]
QED

Theorem assign_base_store_prefix_state_region:
  stmt_state_rel ctx func cenv cx es s0 /\
  declared_storage_region cx mid id subs = SOME (tr,k,tv) /\
  w2n k+type_slot_size tv <= dimword (:256) /\
  (!mid' id' subs' k' tv'.
     declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
     (k',tv') <> (k,tv) ==>
     ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s0.vs_memory /\ encode_value tv v = SOME writes /\
  w2n b+32*(type_slot_size tv-1) < dimword (:256) /\
  write_storage_slot cx tr k tv v es = (INL (),es') ==>
  stmt_state_rel ctx func cenv cx es'
    (store_copy_prefix (if tr then LocTransient else LocStorage)
      b k s0 (type_slot_size tv))
Proof
  strip_tac >>
  `(if (if tr then LocTransient else LocStorage) = LocStorage
    then sstore else tstore) = (if tr then tstore else sstore)` by
    (Cases_on `tr` >> simp[]) >>
  simp[store_copy_prefix_def] >>
  ho_match_mp_tac (cj 2 assign_base_store_state_region) >>
  goal_assum (drule_at (Pat `write_storage_slot _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexistsl_tac [`mid`, `id`, `subs`, `w2n b`, `s0.vs_memory`] >> simp[] >>
  rpt strip_tac >> metis_tac[assign_base_store_source_word, ADD_COMM]
QED

Theorem assign_base_store_control_frame:
  !ctx func cenv cx es s V bb ix prev.
    stmt_state_rel ctx func cenv cx es
      (s with <|vs_vars := V; vs_current_bb := bb;
                vs_inst_idx := ix; vs_prev_bb := prev|>) =
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  rpt gen_tac >>
  `fmp_room ctx func
     (s with <|vs_vars := V; vs_current_bb := bb;
               vs_inst_idx := ix; vs_prev_bb := prev|>) =
   fmp_room ctx func (s with vs_vars := V)` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, immutable_base_zero_alt,
       lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def]
QED

(* execution_frame keeps allocation/log/immutable fields, but permits control
   and scratch-variable changes. The counted continuation must supply it;
   assign_base_store_frame alone deliberately makes no such claim. *)
Theorem assign_base_store_endpoint_state:
  stmt_state_rel ctx func cenv cx es model /\
  local_ptrs_reserved cenv sa /\ execution_frame s = execution_frame model /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x model) ==>
  stmt_state_rel ctx func cenv cx es s
Proof
  strip_tac >>
  `s with <|vs_vars := model.vs_vars; vs_current_bb := model.vs_current_bb;
    vs_inst_idx := model.vs_inst_idx; vs_prev_bb := model.vs_prev_bb|> = model` by
    metis_tac[execution_frame_eq_reconstruct] >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := model.vs_vars)` by
    metis_tac[assign_base_store_control_frame] >>
  `stmt_state_rel ctx func cenv cx es
     ((s with vs_vars := model.vs_vars) with vs_vars := s.vs_vars)` suffices_by simp[] >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

(* The semantic interface consumes exactly the expression endpoint's ordinary
   representation. Robust representation is needed separately by the taint post. *)
Theorem assign_base_store_expr_source:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  stmt_state_rel ctx func cenv cx es1 s /\
  ?b. eval_operand op s = SOME b /\ val_in_memory tv v (w2n b) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[expr_post_def] >> simp[expr_val_rel_def] >> metis_tac[]
QED

(* Ghost postconditions of the complete direct storage-copy prefix. *)
Theory assignBasePtrStorageGhost
Ancestors assignBasePtrStorageSemantic assignBasePtrStorageLoop
  assignBasePtrStorageTaint assignBasePtrStorageFrame appendStorageGhostPtr bodyPtrDefs ptrDiscipline
  venomState compileEnv words arithmetic pred_set finite_map

Theorem assign_base_store_selected_taint_suc:
  (if tr then (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
       b k tn0 (SUC i)).t_trans
   else (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
       b k tn0 (SUC i)).t_stor) =
  key_update
    (if tr then (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
       b k tn0 i).t_trans
     else (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
       b k tn0 i).t_stor)
    (k+n2w i) (mem_word_taint tn0.t_mem (w2n (b+n2w i*32w)))
Proof
  Cases_on `tr` >> simp[assign_base_store_taint_prefix_def]
QED

Theorem assign_base_store_taint_members:
  !n q c.
    w2n k+n <= dimword (:256) /\
    (q,c) IN
      (if tr then (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
         b k tn0 n).t_trans
       else (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
         b k tn0 n).t_stor) ==>
    ((q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
       ~(w2n k <= w2n q /\ w2n q < w2n k+n)) \/
    (?j. w2n q = w2n k+j /\ j<n /\ c<32 /\
         w2n (b+n2w j*32w)+c IN tn0.t_mem)
Proof
  Induct >> rpt gen_tac
  >- simp[assign_base_store_taint_prefix_def] >>
  simp[assign_base_store_selected_taint_suc, key_update_def, mem_word_taint_def] >>
  strip_tac
  >- (first_x_assum (qspecl_then [`q`, `c`] mp_tac) >>
      (impl_tac >- (conj_tac >- decide_tac >> simp[])) >> strip_tac
      >- (disj1_tac >> simp[] >>
          `w2n k+n < dimword (:256)` by decide_tac >>
          `w2n q <> w2n k+n` by
            (strip_tac >>
             `q = k+n2w n` by
               (qpat_x_assum `w2n q = _` (mp_tac o AP_TERM ``n2w:num -> bytes32``) >>
                pure_rewrite_tac[GSYM word_add_n2w, n2w_w2n] >> simp[]) >>
             gvs[]) >> decide_tac) >>
      disj2_tac >> qexists_tac `j` >> simp[] >> metis_tac[ADD_COMM]) >>
  disj2_tac >> qexists_tac `n` >> simp[] >>
  `w2n k+n < dimword (:256)` by decide_tac >>
  `k+n2w n = n2w (w2n k+n)` by simp[GSYM word_add_n2w] >>
  simp[w2n_n2w, LESS_MOD]
QED

Theorem assign_base_store_frame_taint_members:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 n s tn /\ w2n k+n <= dimword (:256) /\
  w2n b+32*(n-1) < dimword (:256) ==>
  !q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
    ((q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
       ~(w2n k <= w2n q /\ w2n q < w2n k+n)) \/
    (?j. w2n q = w2n k+j /\ j<n /\ c<32 /\
         w2n b+32*j+c IN tn0.t_mem)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `(q,c) IN
    (if tr then (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
       b k tn0 n).t_trans
     else (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
       b k tn0 n).t_stor)` by
    (Cases_on `tr` >> gvs[assign_base_store_frame_def]) >>
  `((q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
       ~(w2n k <= w2n q /\ w2n q < w2n k+n)) \/
    (?j. w2n q = w2n k+j /\ j<n /\ c<32 /\
         w2n (b+n2w j*32w)+c IN tn0.t_mem)` by
    metis_tac[assign_base_store_taint_members] >>
  pop_assum strip_assume_tac >- simp[] >>
  disj2_tac >> qexists_tac `j` >> simp[] >>
  `w2n b+32*j < dimword (:256)` by
    (`j <= n-1` by decide_tac >> decide_tac) >>
  `b+n2w j*32w = n2w (w2n b+32*j)` by
    (pure_rewrite_tac[GSYM word_add_n2w, GSYM word_mul_n2w, n2w_w2n] >>
     metis_tac[WORD_MULT_COMM]) >>
  gvs[w2n_n2w, LESS_MOD] >> metis_tac[ADD_COMM, ADD_ASSOC]
QED

Theorem assign_base_store_selected_dead:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (type_slot_size tv) s tn /\
  declared_storage_region cx mid id subs = SOME (tr,k,tv) /\
  (!mid' id' subs' k' tv'.
     declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
     (k',tv') <> (k,tv) ==>
     ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n k+type_slot_size tv <= dimword (:256) /\
  w2n b+32*(type_slot_size tv-1) < dimword (:256) /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
       val_in_memory tv v (w2n b) m) /\
  (!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) ==>
    storage_dead cx tr
      (if tr then contract_transient s0 else contract_storage s0) (w2n q) c) ==>
  !q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
    storage_dead cx tr
      (if tr then contract_transient s else contract_storage s) (w2n q) c
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `storage_dead cx tr final` >>
  qmatch_asmsub_abbrev_tac `storage_dead cx tr initial` >>
  `val_in_memory tv v (w2n b) s0.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes initial) (w2n k) tv i c ==>
    EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
    EL c (word_to_bytes (lookup_storage (n2w i) (apply_writes k writes initial)) T)` by
    (rpt strip_tac >> simp[Abbr `final`] >>
     irule assign_base_store_frame_live >> simp[] >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `!i. i < dimword (:256) /\
    ~(w2n k <= i /\ i < w2n k+type_slot_size tv) ==>
    lookup_storage (n2w i) final = lookup_storage (n2w i) initial` by
    (rpt strip_tac >> simp[Abbr `final`, Abbr `initial`] >>
     irule assign_base_store_frame_outside >> simp[] >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >> simp[]) >>
  drule assign_base_store_frame_taint_members >>
  pure_asm_rewrite_tac[boolTheory.AND_CLAUSES] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==> _` drule >>
  strip_tac
  >- (irule storage_dead_endpoint_outside >>
      goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
      qexists_tac `initial` >> simp[]) >>
  drule_all robust_memory_storage_dead_at_endpoint >> simp[]
QED

Theorem assign_base_store_prefix_opposite:
  !n. (if tr then
    (store_copy_prefix LocTransient b k s0 n).vs_accounts = s0.vs_accounts
    else (store_copy_prefix LocStorage b k s0 n).vs_transient = s0.vs_transient)
Proof
  Induct >> Cases_on `tr` >>
  gvs[assign_base_store_prefix_zero, assign_base_store_prefix_suc,
    sstore_def, tstore_def]
QED

Theorem assign_base_store_opposite_frame:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 n s tn ==>
  tn.t_imm = tn0.t_imm /\
  (if tr then
     tn.t_stor = tn0.t_stor /\ s.vs_accounts = s0.vs_accounts
   else tn.t_trans = tn0.t_trans /\ s.vs_transient = s0.vs_transient)
Proof
  strip_tac >>
  qspec_then `n` mp_tac assign_base_store_prefix_opposite >>
  Cases_on `tr` >> gvs[assign_base_store_frame_def, assign_base_store_taint_frame]
QED

Theorem assign_base_store_initial_selected_dead:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target ==>
  !q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
    storage_dead cx tr
      (if tr then contract_transient s else contract_storage s) (w2n q) c
Proof
  Cases_on `tr` >>
  simp[stor_taint_ok_def, cx_dead_def, SUBSET_DEF,
    contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem assign_base_store_stor_taint_ok:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (type_slot_size tv) s tn /\
  stor_taint_ok cx tn0 s0 /\ s0.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid id subs = SOME (tr,k,tv) /\
  (!mid' id' subs' k' tv'.
     declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
     (k',tv') <> (k,tv) ==>
     ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n k+type_slot_size tv <= dimword (:256) /\
  w2n b+32*(type_slot_size tv-1) < dimword (:256) /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
       val_in_memory tv v (w2n b) m) ==>
  stor_taint_ok cx tn s
Proof
  strip_tac >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) ==>
    storage_dead cx tr (if tr then contract_transient s0 else contract_storage s0)
      (w2n q) c` by
    (rpt strip_tac >> irule assign_base_store_initial_selected_dead >> simp[] >>
     qexists_tac `tn0` >> simp[]) >>
  drule assign_base_store_selected_dead >>
  pure_asm_rewrite_tac[boolTheory.AND_CLAUSES] >> strip_tac >>
  drule assign_base_store_opposite_frame >> strip_tac >>
  `s.vs_call_ctx = s0.vs_call_ctx` by gvs[assign_base_store_frame_def] >>
  irule stor_taint_ok_selected_space >> simp[] >>
  qexistsl_tac [`s0`, `tn0`, `tr`] >> simp[] >>
  Cases_on `tr` >> gvs[contract_storage_def, contract_transient_def,
    vfmStateTheory.lookup_account_def] >> metis_tac[]
QED

(* The generic old-variable transport already handles all local/return
   pointer clauses. Storage-copy consumers only supply the new storage post. *)
Theorem assign_base_store_ghost_post:
  ghost_inv d cenv cx es G0 tn0 s0 /\
  assign_base_store_frame loc b k s0 tn0 n s tn /\
  stor_taint_ok cx tn s /\ es'.scopes = es.scopes /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x) /\
    lookup_var x s = lookup_var x s0) ==>
  ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  `s.vs_memory = s0.vs_memory /\ tn.t_mem = tn0.t_mem` by
    gvs[assign_base_store_frame_def] >>
  conj_tac
  >- (irule ghost_inv_old_transport >> simp[] >>
      goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
      qexists_tac `sa` >> simp[]) >>
  irule ghost_kept_old_transport >> simp[]
QED

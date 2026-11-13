(* Active storage prefixes preserve the declared root's taint invariant. *)
Theory assignSubregionPtrStoragePrefix
Ancestors
  assignSubregionPtrStorageGhost assignStoragePrefixLivePtr
  assignBasePtrStorageGhost storageSubregionFrame assignBasePtrStorageTaint
  assignBasePtrStorageFrame assignBasePtrStorageSemantic assignBasePtrStorageLoop
  compileEnv loweringStateRelDefs vyperStoragePlaceRegion
  venomState bodyPtrDefs ptrDiscipline words arithmetic pred_set

Theorem assign_base_store_subregion_prefix_selected_dead:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 copied s tn /\ copied <= type_slot_size tv /\
  declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ w2n k = w2n root + delta /\
  w2n root + type_slot_size rtv <= dimword (:256) /\
  (!mid' id' subs' root' rtv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,root',rtv') /\
    (root',rtv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size rtv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n b+32*(copied-1) < dimword (:256) /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory tv v (w2n b) m) /\
  (!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes
      (if tr then contract_transient s0 else contract_storage s0)) (w2n k) tv i c ==>
    i < w2n k+copied) /\
  (!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
    w2n k+copied <= w2n q /\ w2n q < w2n k+type_slot_size tv ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n k) tv (w2n q) c) /\
  (!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) ==>
    storage_dead cx tr
      (if tr then contract_transient s0 else contract_storage s0) (w2n q) c) ==>
  !q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
    storage_dead cx tr
      (if tr then contract_transient s else contract_storage s) (w2n q) c
Proof
  strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n k+type_slot_size tv <= dimword (:256) /\
   w2n k+copied <= dimword (:256)` by decide_tac >>
  `val_in_memory tv v (w2n b) s0.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes
      (if tr then contract_transient s0 else contract_storage s0)) (w2n k) tv i c ==>
    EL c (word_to_bytes (lookup_storage (n2w i)
      (if tr then contract_transient s else contract_storage s)) T) =
    EL c (word_to_bytes (lookup_storage (n2w i) (apply_writes k writes
      (if tr then contract_transient s0 else contract_storage s0))) T)` by
    (rpt strip_tac >>
     `i < w2n k+copied` by metis_tac[] >>
     irule assign_base_store_frame_live_prefix >> simp[] >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `!w:bytes32. ~(w2n root+delta <= w2n w /\
      w2n w < w2n root+delta+type_slot_size tv) ==>
    lookup_storage w (if tr then contract_transient s else contract_storage s) =
    lookup_storage w (if tr then contract_transient s0 else contract_storage s0)` by
    (rpt strip_tac >>
     `~(w2n k <= w2n w /\ w2n w < w2n k+copied)` by (gnvs[] >> decide_tac) >>
     `w2n (w:bytes32) < dimword (:256)` by metis_tac[w2n_lt] >>
     `lookup_storage (n2w (w2n w))
        (if tr then contract_transient s else contract_storage s) =
      lookup_storage (n2w (w2n w))
        (if tr then contract_transient s0 else contract_storage s0)` suffices_by simp[] >>
     mp_tac (Q.INST [`b` |-> `b`, `k` |-> `k`, `tn0` |-> `tn0`,
       `tn` |-> `tn`, `n` |-> `copied`, `tr` |-> `tr`,
       `s` |-> `s`, `s0` |-> `s0`, `x` |-> `w2n (w:bytes32)`]
       (SPEC_ALL assign_base_store_frame_outside)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  drule assign_base_store_frame_taint_members >>
  pure_asm_rewrite_tac[boolTheory.AND_CLAUSES] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule storage_subregion_copy_taint_at_endpoint >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
  simp[] >>
  qexistsl_tac [`copied`,`id`,`k`,`s0.vs_memory`,`mid`,
    `if tr then tn.t_trans else tn.t_stor`,`w2n (b:bytes32)`,
    `if tr then tn0.t_trans else tn0.t_stor`,
    `if tr then contract_transient s0 else contract_storage s0`,`subs`,`tn0.t_mem`] >>
  simp[] >>
  qpat_x_assum `!q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM,DE_MORGAN_THM]

QED

Theorem assign_base_store_subregion_prefix_stor_taint_ok:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 copied s tn /\ copied <= type_slot_size tv /\
  stor_taint_ok cx tn0 s0 /\ s0.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ w2n k = w2n root + delta /\
  w2n root + type_slot_size rtv <= dimword (:256) /\
  (!mid' id' subs' root' rtv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,root',rtv') /\
    (root',rtv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size rtv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n b+32*(copied-1) < dimword (:256) /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory tv v (w2n b) m) /\
  (!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes
      (if tr then contract_transient s0 else contract_storage s0)) (w2n k) tv i c ==>
    i < w2n k+copied) /\
  (!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
    w2n k+copied <= w2n q /\ w2n q < w2n k+type_slot_size tv ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n k) tv (w2n q) c) ==>
  stor_taint_ok cx tn s
Proof
  strip_tac >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) ==>
    storage_dead cx tr (if tr then contract_transient s0 else contract_storage s0)
      (w2n q) c` by
    (rpt strip_tac >> irule assign_base_store_initial_selected_dead >> simp[] >>
     qexists_tac `tn0` >> simp[]) >>
  drule assign_base_store_subregion_prefix_selected_dead >>
  pure_asm_rewrite_tac[boolTheory.AND_CLAUSES] >> strip_tac >>
  drule assign_base_store_opposite_frame >> strip_tac >>
  `s.vs_call_ctx = s0.vs_call_ctx` by gvs[assign_base_store_frame_def] >>
  irule stor_taint_ok_selected_space >> simp[] >>
  qexistsl_tac [`s0`,`tn0`,`tr`] >> simp[] >>
  Cases_on `tr` >> gvs[contract_storage_def, contract_transient_def,
    vfmStateTheory.lookup_account_def] >> metis_tac[]
QED

(* Dead bytes copied into a storage child remain dead in its declared root. *)
Theory assignSubregionPtrStorageGhost
Ancestors
  assignBasePtrStorageGhost storageSubregionFrame storageDynPrefixLive assignBasePtrStorageTaint
  assignBasePtrStorageFrame assignBasePtrStorageSemantic assignBasePtrStorageLoop
  compileEnv loweringStateRelDefs vyperStoragePlaceRegion accountsRelProps
  venomState bodyPtrDefs ptrDiscipline words arithmetic pred_set

Theorem robust_memory_subregion_storage_dead_at_endpoint:
  !cx tr mid id subs root rtv path delta tv v writes k st final ta mem off j c.
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
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    (!i b. w2n k <= i /\ i < w2n k + type_slot_size tv /\ b < 32 /\
      ~dead_bytes (apply_writes k writes st) (w2n k) tv i b ==>
      EL b (word_to_bytes (lookup_storage (n2w i) final) T) =
      EL b (word_to_bytes (lookup_storage (n2w i)
        (apply_writes k writes st)) T)) /\
    j < type_slot_size tv /\ c < 32 /\ off + 32*j + c IN ta ==>
    storage_dead cx tr final (w2n k+j) c
Proof
  rpt gen_tac >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n k + type_slot_size tv <= dimword (:256)` by decide_tac >>
  `dead_bytes final (w2n k) tv (w2n k+j) c` by
    (irule robust_memory_taint_dead_at_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     qexistsl_tac [`mem`,`off`,`st`,`ta`] >> simp[] >>
     `c + (32*j + off) = off + 32*j + c` by decide_tac >> asm_rewrite_tac[]) >>
  `dead_bytes final (w2n root) rtv (w2n k+j) c` by
    (irule storage_subregion_dead_bytes >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     metis_tac[ADD_COMM,ADD_ASSOC]) >>
  irule declared_region_dead_storage_dead >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >> simp[] >>
  qexistsl_tac [`mid`,`id`,`subs`] >> simp[]
QED

Theorem dynarray_after_live_prefix_dead:
  !st start et cap n j b.
    lookup_storage (n2w start) st = n2w n /\ n < dimword (:256) /\ b < 32 /\
    start+1+n*type_slot_size et <= j /\
    j < start+1+cap*type_slot_size et ==>
    dead_bytes st start (ArrayTV et (Dynamic cap)) j b
Proof
  rpt gen_tac >> strip_tac >> spose_not_then assume_tac >>
  `start <= j` by decide_tac >>
  drule_all dynarray_live_prefix >> simp[w2n_n2w,LESS_MOD] >> decide_tac
QED

Theorem dynarray_retained_tail_dead:
  lookup_storage (n2w start) final = n2w n /\ n < dimword (:256) /\
  (!q b. (q,b) IN old ==> storage_dead cx tr initial (w2n q) b) ==>
  !q b. (q,b) IN old /\ start+1+n*type_slot_size et <= w2n q /\
    w2n q < start+1+cap*type_slot_size et ==>
    dead_bytes final start (ArrayTV et (Dynamic cap)) (w2n q) b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `storage_dead cx tr initial (w2n q) b` by metis_tac[] >>
  `b < 32` by
    (qpat_x_assum `storage_dead _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [storage_dead_def]) >>
     drule (cj 1 dead_bytes_range) >> simp[]) >>
  mp_tac (Q.SPECL [`final`,`start`,`et`,`cap`,`n`,`w2n q`,`b`]
    dynarray_after_live_prefix_dead) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

(* A dynamic copy may retain old taint beyond the live prefix. *)
Theorem storage_subregion_copy_taint_at_endpoint:
  !cx tr mid id subs root rtv path delta k tv v writes st final ta mem off count old new.
    declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
    storage_subregion rtv path delta tv /\ w2n k = w2n root+delta /\
    w2n root+type_slot_size rtv <= dimword (:256) /\
    (!mid' id' subs' root' rtv'.
      declared_storage_region cx mid' id' subs' = SOME (tr,root',rtv') /\
      (root',rtv') <> (root,rtv) ==>
      ranges_disjoint (w2n root) (type_slot_size rtv)
                      (w2n root') (type_slot_size rtv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\ count <= type_slot_size tv /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    (!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
      ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
      EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
      EL c (word_to_bytes (lookup_storage (n2w i)
        (apply_writes k writes st)) T)) /\
    (!w:bytes32. ~(w2n root+delta <= w2n w /\
      w2n w < w2n root+delta+type_slot_size tv) ==>
      lookup_storage w final = lookup_storage w st) /\
    (!q b. (q,b) IN old ==> storage_dead cx tr st (w2n q) b) /\
    (!q b. (q,b) IN old /\ w2n k+count <= w2n q /\
      w2n q < w2n k+type_slot_size tv ==>
      dead_bytes final (w2n k) tv (w2n q) b) /\
    (!q b. (q,b) IN new ==>
      ((q,b) IN old /\ ~(w2n k <= w2n q /\ w2n q < w2n k+count)) \/
      (?j. w2n q = w2n k+j /\ j<count /\ b<32 /\ off+32*j+b IN ta)) ==>
    !q b. (q,b) IN new ==> storage_dead cx tr final (w2n q) b
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q b. (q,b) IN new ==> _` drule >> strip_tac
  >- (Cases_on `w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv`
      >- (`dead_bytes final (w2n k) tv (w2n q) b` by
            (first_x_assum irule >> simp[] >> decide_tac) >>
          `dead_bytes final (w2n root) rtv (w2n q) b` by
            (irule storage_subregion_dead_bytes >>
             goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
             metis_tac[ADD_COMM,ADD_ASSOC]) >>
          irule declared_region_dead_storage_dead >>
          goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >> simp[] >>
          qexistsl_tac [`mid`,`id`,`subs`] >> simp[]) >>
      `storage_dead cx tr final (w2n q) b <=> storage_dead cx tr st (w2n q) b` by
        (irule storage_dead_subregion_frame_outside >>
         goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
         goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >> simp[]) >>
      metis_tac[]) >>
  `j < type_slot_size tv` by decide_tac >>
  drule_all robust_memory_subregion_storage_dead_at_endpoint >> simp[]
QED

Theorem assign_base_store_subregion_selected_dead:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (type_slot_size tv) s tn /\
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
  drule storage_subregion_bounds >> strip_tac >>
  `w2n k + type_slot_size tv <= dimword (:256)` by decide_tac >>
  `val_in_memory tv v (w2n b) s0.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes initial) (w2n k) tv i c ==>
    EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
    EL c (word_to_bytes (lookup_storage (n2w i)
      (apply_writes k writes initial)) T)` by
    (rpt strip_tac >> simp[Abbr `final`] >>
     irule assign_base_store_frame_live >> simp[] >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >> gnvs[]) >>
  `!w:bytes32. ~(w2n root + delta <= w2n w /\
      w2n w < w2n root + delta + type_slot_size tv) ==>
    lookup_storage w final = lookup_storage w initial` by
    (rpt strip_tac >> simp[Abbr `final`, Abbr `initial`] >>
     `lookup_storage (n2w (w2n w))
        (if tr then contract_transient s else contract_storage s) =
      lookup_storage (n2w (w2n w))
        (if tr then contract_transient s0 else contract_storage s0)` suffices_by simp[] >>
     mp_tac (Q.INST [`b` |-> `b`, `k` |-> `k`, `tn0` |-> `tn0`,
       `tn` |-> `tn`, `n` |-> `type_slot_size tv`, `tr` |-> `tr`,
       `s` |-> `s`, `s0` |-> `s0`, `x` |-> `w2n (w:bytes32)`]
       (SPEC_ALL assign_base_store_frame_outside)) >>
     (impl_tac >- (gnvs[] >> metis_tac[w2n_lt])) >> simp[]) >>
  drule assign_base_store_frame_taint_members >>
  pure_asm_rewrite_tac[boolTheory.AND_CLAUSES] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==> _` drule >>
  strip_tac
  >- (`storage_dead cx tr final (w2n q) c <=>
       storage_dead cx tr initial (w2n q) c` by
        (irule storage_dead_subregion_frame_outside >>
         goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
         goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >> simp[]) >>
      metis_tac[]) >>
  drule_all robust_memory_subregion_storage_dead_at_endpoint >> simp[]
QED

Theorem assign_base_store_subregion_stor_taint_ok:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (type_slot_size tv) s tn /\
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
  drule assign_base_store_subregion_selected_dead >>
  pure_asm_rewrite_tac[boolTheory.AND_CLAUSES] >> strip_tac >>
  drule assign_base_store_opposite_frame >> strip_tac >>
  `s.vs_call_ctx = s0.vs_call_ctx` by gvs[assign_base_store_frame_def] >>
  irule stor_taint_ok_selected_space >> simp[] >>
  qexistsl_tac [`s0`,`tn0`,`tr`] >> simp[] >>
  Cases_on `tr` >> gvs[contract_storage_def, contract_transient_def,
    vfmStateTheory.lookup_account_def] >> metis_tac[]
QED

(* Land the existing sparse storage pointer execution in the source state. *)
Theory assignSparseStorageLandingPtr
Ancestors
  storeSlotsPtrInterface placeStoreSlots placeStoreStorage
  assignBasePtrStorageSemantic assignBasePtrStorageGhost stmtSimStoreCopy
  bodyPtrPopNestedLiveGhost vyperInterpreter vyperState
  assignBasePtrStorageTaint assignBasePtrStorageFrame appendStorageGhostPtr accountsRelProps
  bodyPtrDefs exprSimHypsDefs exprLoweringProps vyperStoragePlaceRegion
  vyperStorageBackend vyperTyping compileEnv context loweringStateRelDefs
  venomState valueEncoding valueEncodingDefs vyperEncodeDecode ptrDiscipline arithmetic words
  finite_map list pred_set

Theorem sparse_store_taint_members:
  !ks old q c.
    (q,c) IN FOLDL (\ta j. key_update ta (dw+n2w j)
      (mem_word_taint ta0 (off+32*j))) old ks ==>
    ((q,c) IN old /\ !j. MEM j ks ==> q <> dw+n2w j) \/
    (?j. MEM j ks /\ q = dw+n2w j /\ c < 32 /\ off+32*j+c IN ta0)
Proof
  Induct >> simp_tac std_ss [FOLDL,MEM] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[key_update_def,mem_word_taint_def] >>
  metis_tac[]
QED
Theorem sparse_store_retained_dead:
  expr_sim_inv ce cx env es /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,rootv) /\
  storage_subregion rootv path delta tv /\ start = w2n rootk+delta /\
  0 < type_slot_size tv /\ start+type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  storage_dead cx tr st (w2n q) c /\
  (!j. MEM j (MAP FST writes) ==> q <> n2w (start+j)) ==>
  storage_dead cx tr (apply_writes (n2w start) writes st) (w2n q) c
Proof
  strip_tac >> drule_all place_store_root_layout >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  Cases_on `start <= w2n q /\ w2n q < start+type_slot_size tv`
  >- (`c < 32` by
        (qpat_x_assum `storage_dead _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [storage_dead_def]) >>
         drule (cj 1 dead_bytes_range) >> simp[]) >>
      `dead_bytes st start tv (w2n q) c` by
        (spose_not_then assume_tac >>
         mp_tac (Q.SPECL [`cx`,`tr`,`mid`,`name`,`subs`,`rootk`,`rootv`,
           `path`,`delta`,`tv`,`st`,`w2n q`,`c`] place_store_subregion_not_dead) >>
         (impl_tac >- (rpt conj_tac >> fs[] >> metis_tac[])) >> simp[]) >>
      `start+(w2n q-start) = w2n q` by decide_tac >>
      `w2n q-start < type_slot_size tv` by decide_tac >>
      `~MEM (w2n q-start) (MAP FST writes)` by
        (strip_tac >>
         `q <> n2w (start+(w2n q-start))` by metis_tac[] >>
         qpat_x_assum `q <> n2w (start+(w2n q-start))` mp_tac >>
         asm_rewrite_tac[n2w_w2n]) >>
      `dead_bytes (apply_writes (n2w start) writes st) start tv (w2n q) c` by
        (spose_not_then assume_tac >>
         qpat_x_assum `start = w2n rootk+delta` kall_tac >>
         mp_tac (Q.SPECL [`tv`,`v`,`writes`,`st`,`start`,`w2n q-start`,`c`]
           place_store_unwritten_live_preserved) >>
         asm_rewrite_tac[]) >>
      `dead_bytes (apply_writes (n2w start) writes st)
        (w2n rootk) rootv (w2n q) c` by
        (irule place_store_dead_subregion >>
         goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
         metis_tac[]) >>
      irule declared_region_dead_storage_dead >>
      goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
      simp[] >> qexistsl_tac [`mid`,`name`,`subs`] >> simp[]) >>
  irule place_store_storage_dead_subregion_frame >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  qexists_tac `st` >> simp[] >> qx_gen_tac `key` >> disch_tac >>
  `lookup_storage (n2w (w2n key)) (apply_writes (n2w start) writes st) =
    lookup_storage (n2w (w2n key)) st` suffices_by simp[] >>
  irule encoded_storage_lookup_outside >>
  conj_tac >- simp[w2n_lt] >>
  qexistsl_tac [`tv`,`v`] >> simp[w2n_n2w] >> decide_tac
QED

Theorem sparse_store_taint_dead:
  expr_sim_inv ce cx env es /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,rootv) /\
  storage_subregion rootv path delta tv /\ start = w2n rootk+delta /\
  0 < type_slot_size tv /\ start+type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ encode_value tv v = SOME writes /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v (w2n sw) m) /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  (!q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
    storage_dead cx tr st (w2n q) c) ==>
  !q c. (q,c) IN store_slots_taint tr sw (n2w start) tn ks ==>
    storage_dead cx tr (apply_writes (n2w start) writes st) (w2n q) c
Proof
  strip_tac >> drule_all place_store_root_layout >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  rpt gen_tac >> rewrite_tac[store_slots_taint_def] >> strip_tac >>
  drule sparse_store_taint_members >> strip_tac
  >- (irule sparse_store_retained_dead >> rpt conj_tac
      >- metis_tac[word_add_n2w]
      >- (qexistsl_tac [`ce`,`env`,`es`] >> asm_rewrite_tac[])
      >- (qexistsl_tac [`delta`,`mid`,`name`,`path`,`rootk`,`rootv`,`subs`,`tv`,`v`] >>
          asm_rewrite_tac[])
      >> metis_tac[]) >>
  `j < type_slot_size tv` by
    (irule (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >> simp[] >> metis_tac[]) >>
  `start+j < dimword (:256)` by decide_tac >>
  `w2n q = start+j` by
    (qpat_x_assum `q = n2w start+n2w j`
       (fn th => pure_rewrite_tac[th,word_add_n2w,w2n_n2w]) >>
     irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  `MEM j (MAP FST writes)` by metis_tac[] >>
  `w2n (n2w start : bytes32) = start` by
    (pure_rewrite_tac[w2n_n2w] >> irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  `dead_bytes (apply_writes (n2w start) writes st) start tv (w2n q) c` by
    (qpat_x_assum `w2n q = start+j` SUBST1_TAC >>
     qpat_x_assum `w2n (n2w start : bytes32) = start`
       (fn th => mp_tac (REWRITE_RULE [th]
         (Q.SPECL [`tv`,`v`,`writes`,`n2w start`,`st`,`tn.t_mem`,`mem`,
           `w2n (sw:bytes32)`,`j`,`c`] robust_memory_taint_dead))) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `dead_bytes (apply_writes (n2w start) writes st)
    (w2n rootk) rootv (w2n q) c` by
    (irule place_store_dead_subregion >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >> metis_tac[]) >>
  irule declared_region_dead_storage_dead >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`mid`,`name`,`subs`] >> simp[]
QED


Theorem store_slots_ptr_storage_landing:
  !d ce cx env es ctx fn sa ty tv v sw start tr mid name subs
    rootk rootv path delta writes ks s G tn t H tf.
    stmt_state_rel ctx fn ce cx es s /\ expr_sim_inv ce cx env es /\
    ghost_inv d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ encode_value tv v = SOME writes /\
    declared_storage_region cx mid name subs = SOME (tr,rootk,rootv) /\
    storage_subregion rootv path delta tv /\ start = w2n rootk+delta /\
    0 < type_slot_size tv /\ start+type_slot_size tv <= dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n sw) m) /\
    store_slots_ptr_frame tr sw (n2w start) s tn ks t tf /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx ==>
    stmt_state_rel ctx fn ce cx
      (set_storage cx es tr
        (apply_writes (n2w start) writes (get_storage cx es tr))) t /\
    ghost_inv d ce cx
      (set_storage cx es tr
        (apply_writes (n2w start) writes (get_storage cx es tr))) H tf t /\
    ghost_kept ce es sa G tn s H tf
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `store_slots_ptr_frame _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [store_slots_ptr_frame_def]) >>
  `start < dimword (:256)` by decide_tac >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 evaluate_type_well_formed] >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  qabbrev_tac `fin = set_storage cx es tr
    (apply_writes (n2w start) writes (get_storage cx es tr))` >>
  `stmt_state_rel ctx fn ce cx fin (store_copy_normalize s t)` by
    (simp[Abbr `fin`] >>
     qpat_x_assum `store_copy_normalize s t = _` SUBST1_TAC >>
     qspecl_then [`ce`,`cx`,`env`,`es`,`ctx`,`fn`,`s`,`mid`,`name`,`subs`,
       `tr`,`rootk`,`rootv`,`path`,`delta`,`tv`,`start`,`writes`,`v`,`ks`,
       `\i. mload (w2n (sw:bytes32)+32*i) s`] mp_tac
       place_store_encoded_leaf_state_sparse >>
     (impl_tac >- (rpt conj_tac
       >~ [`EL _ (word_to_bytes _ _)`]
       >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
           irule place_store_memory_live_at >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- first_assum ACCEPT_TAC >>
           qexistsl_tac [`tv`,`v`] >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
       first_assum ACCEPT_TAC)) >>
     simp[GSYM word_add_n2w]) >>
  `stmt_state_rel ctx fn ce cx fin t` by
    (irule place_store_normalized_stmt_state >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
     qexists_tac `s` >> simp[] >> metis_tac[]) >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def] >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
    (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s)` by
    (qpat_x_assum `stmt_state_rel ctx fn ce cx es s` mp_tac >>
     Cases_on `tr` >> simp[stmt_state_rel_def,state_rel_def,accounts_rel_def,
       accounts_agree_def,transient_agree_def,get_storage_def,
       vfmStateTheory.lookup_account_def,contract_storage_def,
       contract_transient_def,call_ctx_rel_def] >> metis_tac[]) >>
  `storage_dead cx tr (if tr then contract_transient s else contract_storage s) =
    storage_dead cx tr (get_storage cx es tr)` by
    metis_tac[storage_agree_storage_dead] >>
  `storage_agree (storage_dead cx tr (get_storage cx fin tr))
    (get_storage cx fin tr)
    (if tr then contract_transient t else contract_storage t)` by
    (qpat_x_assum `stmt_state_rel ctx fn ce cx fin t` mp_tac >>
     Cases_on `tr` >> simp[stmt_state_rel_def,state_rel_def,accounts_rel_def,
       accounts_agree_def,transient_agree_def,get_storage_def,
       vfmStateTheory.lookup_account_def,contract_storage_def,
       contract_transient_def,call_ctx_rel_def] >> metis_tac[]) >>
  `storage_dead cx tr (if tr then contract_transient t else contract_storage t) =
    storage_dead cx tr (get_storage cx fin tr)` by
    metis_tac[storage_agree_storage_dead] >>
  `!q c. (q,c) IN (if tr then tf.t_trans else tf.t_stor) ==>
    storage_dead cx tr (if tr then contract_transient t else contract_storage t)
      (w2n q) c` by
    (`get_storage cx fin tr = apply_writes (n2w start) writes
       (get_storage cx es tr)` by simp[Abbr `fin`,get_storage_after_set] >>
     `!q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
       storage_dead cx tr (get_storage cx es tr) (w2n q) c` by
       (rpt gen_tac >> strip_tac >>
        qpat_x_assum `storage_dead cx tr
          (if tr then contract_transient s else contract_storage s) = _`
          (fn th => once_rewrite_tac[GSYM th]) >>
        irule assign_base_store_initial_selected_dead >> simp[] >>
        qexists_tac `tn` >> fs[ghost_inv_def]) >>
     mp_tac (Q.INST [`st` |-> `get_storage cx es tr`,
                     `mem` |-> `s.vs_memory`] sparse_store_taint_dead) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_rewrite_tac[]) >>
  `(if tr then t.vs_accounts = s.vs_accounts else
      t.vs_transient = s.vs_transient)` by
    (Cases_on `tr`
     >- (qpat_x_assum `store_copy_normalize s t = _`
           (mp_tac o AP_TERM ``\z:venom_state. z.vs_accounts``) >>
         simp[assign_base_store_backend_fold,store_copy_normalize_def]) >>
     qpat_x_assum `store_copy_normalize s t = _`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_transient``) >>
     simp[assign_base_store_backend_fold,store_copy_normalize_def]) >>
  `stor_taint_ok cx tf t` by
    (irule stor_taint_ok_selected_space >> simp[] >>
     qexistsl_tac [`s`,`tn`,`tr`] >> simp[] >>
     fs[ghost_inv_def] >> Cases_on `tr` >>
     fs[contract_storage_def,contract_transient_def,vfmStateTheory.lookup_account_def] >>
     metis_tac[ADD_COMM]) >>
  `ghost_inv d ce cx fin H tf t` by
    (irule pop_header_ghost_transport >> simp[] >>
     qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >> simp[] >>
     simp[Abbr `fin`] >> fs[ghost_inv_def] >> metis_tac[]) >>
  `ghost_kept ce es sa G tn s H tf` by
    (irule ghost_kept_old_transport >> simp[] >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

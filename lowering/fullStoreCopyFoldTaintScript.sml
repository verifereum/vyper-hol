(* Raw finite store folds expose one storage-taint boundary. *)
Theory fullStoreCopyFoldTaint
Ancestors fullStoreCopyTaint storageCopyBackendFold placeStoreSlots
  storageCopyLive valueEncodingProps venomState venomMemDefs stmtSimStoreCopy
  words arithmetic list rich_list pred_set

Theorem store_copy_fold_stor_taint_ok:
  declared_storage_region cx mid n subs = SOME (tr,(k:bytes32),tv) /\
  MEM (tr,k,tv) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword(:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v off m) /\
  store_copy_normalize s u =
    FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
      (mload (off+32*i) s) q) s ks /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta i. key_update ta (k+n2w i)
      (mem_word_taint tn.t_mem (off+32*i)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans) /\
  tf.t_imm = tn.t_imm /\ (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_call_ctx.cc_address = cx.txn.target /\
  stor_taint_ok H cx tn s ==>
  stor_taint_ok H cx tf u
Proof
  strip_tac >>
  `val_in_memory tv v off s.vs_memory` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  qabbrev_tac `st = if tr then s.vs_transient s.vs_call_ctx.cc_address
    else (s.vs_accounts s.vs_call_ctx.cc_address).storage` >>
  qabbrev_tac `final = if tr then u.vs_transient u.vs_call_ctx.cc_address
    else (u.vs_accounts u.vs_call_ctx.cc_address).storage` >>
  `final = FOLDL (\q i. update_storage (k+n2w i) (mload (off+32*i) s) q) st ks /\
   (if tr then (u.vs_accounts u.vs_call_ctx.cc_address).storage =
     (s.vs_accounts s.vs_call_ctx.cc_address).storage
    else u.vs_transient u.vs_call_ctx.cc_address =
     s.vs_transient s.vs_call_ctx.cc_address)` by suspend "projection" >>
  `cx.txn.target = s.vs_call_ctx.cc_address` by metis_tac[] >>
  irule store_copy_live_stor_taint_ok >> simp[] >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexistsl_tac [`s.vs_memory`,`off`,`s`,`tn.t_mem`,`tn`,`v`,`writes`] >>
  simp[] >>
  conj_tac >- suspend "live" >>
  conj_tac >- suspend "outside" >>
  reverse conj_tac >- (Cases_on `tr` >> gvs[]) >> suspend "taint"
QED
Resume store_copy_fold_stor_taint_ok[projection]:
  qpat_x_assum `store_copy_normalize s u = _` mp_tac >>
  simp[storage_copy_backend_fold, store_copy_normalize_def] >>
  Cases_on `tr` >>
  simp[Abbr `st`, Abbr `final`, venomStateTheory.contract_storage_def,
    venomStateTheory.contract_transient_def, vfmStateTheory.lookup_account_def,
    combinTheory.APPLY_UPDATE_THM] >>
  simp[venomStateTheory.venom_state_component_equality] >> strip_tac >> gvs[]
QED
Resume store_copy_fold_stor_taint_ok[taint]:
  qspecl_then [`ks`,`if tr then tn.t_trans else tn.t_stor`]
    mp_tac (Q.INST [`M` |-> `tn.t_mem`] store_copy_live_taint_bound) >>
  qpat_x_assum `!i. MEM i ks <=> _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[AC ADD_ASSOC ADD_COMM] >> simp[]
QED
Resume store_copy_fold_stor_taint_ok[live]:
  ` (if tr then u.vs_transient s.vs_call_ctx.cc_address
     else (u.vs_accounts s.vs_call_ctx.cc_address).storage) = final` by
    (qpat_assum `u.vs_call_ctx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[Abbr `final`, NoAsms]) >> pop_assum SUBST1_TAC >>
  rpt strip_tac >> qabbrev_tac `j = i - w2n k` >>
  `i = w2n k + j /\ j < type_slot_size tv /\ i < dimword(:256)` by
    (simp[Abbr `j`] >> decide_tac) >>
  `lookup_storage (n2w i) final =
    if MEM j ks then mload (off+32*j) s else lookup_storage (n2w i) st`
    by suspend "lookup" >>
  Cases_on `MEM j ks`
  >- (simp[] >>
      drule_at (Pat `val_in_memory _ _ _ _`) encode_value_memory_live >>
      disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
      disch_then (qspecl_then [`k`,`st`,`j`,`c`] mp_tac) >>
      simp[mem_word_at_eq_mload] >> gvs[] >> metis_tac[]) >>
  `lookup_storage (n2w i) (apply_writes k writes st) =
    lookup_storage (n2w i) st` by suspend "unwritten" >> simp[]
QED
Resume store_copy_fold_stor_taint_ok[outside]:
  ` (if tr then u.vs_transient s.vs_call_ctx.cc_address
     else (u.vs_accounts s.vs_call_ctx.cc_address).storage) = final` by
    (qpat_assum `u.vs_call_ctx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[Abbr `final`, NoAsms]) >> pop_assum SUBST1_TAC >>
  qpat_x_assum `final = _` SUBST1_TAC >> rpt strip_tac >>
  irule (SRULE [FOLDL_MAP] (Q.ISPEC
    `MAP (\j. ((k:bytes32)+n2w j,mload (off+32*j) s)) ks` placeStoreStorageTheory.place_store_updates_miss)) >>
  pure_rewrite_tac[MAP_MAP_o, combinTheory.o_DEF, pairTheory.FST] >>
  simp[NoAsms, MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM x ks` >>
  `x < type_slot_size tv` by metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `w2n k + x < dimword(:256) /\ x < dimword(:256)` by decide_tac >>
  `i = w2n k + x` by
    (qpat_x_assum `(n2w i):bytes32 = _` (mp_tac o Q.AP_TERM `w2n`) >>
     pure_rewrite_tac[w2n_add_2, w2n_n2w] >>
     `i < dimword(:256)` by decide_tac >>
     asm_simp_tac pure_ss [w2n_add_2, w2n_n2w, LESS_MOD] >> simp[] ) >> decide_tac
QED
Resume store_copy_fold_stor_taint_ok[lookup]:
  `!x. MEM x ks ==> x < type_slot_size tv` by
    metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `!x. MEM x ks ==> ((k + n2w x):bytes32 = n2w i <=> x = j)` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     `x < dimword(:256) /\ w2n k+x < dimword(:256)` by decide_tac >>
     once_rewrite_tac[GSYM w2n_11] >>
     asm_simp_tac pure_ss [w2n_add_2, w2n_n2w, LESS_MOD] >>
     decide_tac) >>
  qpat_x_assum `final = _` SUBST1_TAC >>
  Cases_on `MEM j ks` >> asm_rewrite_tac[]
  >- (irule (SRULE [FOLDL_MAP] (Q.ISPEC
        `MAP (\x. ((k:bytes32)+n2w x,mload (off+32*x) s)) ks`
        placeStoreStorageTheory.place_store_updates_hit)) >>
      pure_rewrite_tac[MEM_MAP, pairTheory.FORALL_PROD,
        pairTheory.FST, pairTheory.SND, pairTheory.PAIR_EQ] >>
      reverse conj_tac
      >- (qexists_tac `j` >> simp[] >> metis_tac[ADD_SYM]) >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  irule (SRULE [FOLDL_MAP] (Q.ISPEC
    `MAP (\x. ((k:bytes32)+n2w x,mload (off+32*x) s)) ks`
    placeStoreStorageTheory.place_store_updates_miss)) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_MAP]
QED
Resume store_copy_fold_stor_taint_ok[unwritten]:
  `k = (n2w (w2n k):bytes32)` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  qpat_assum `i = w2n k + j` (fn th => pure_rewrite_tac[th]) >>
  irule vyperEncodeDecodeTheory.apply_writes_lookup_miss_num >>
  rpt strip_tac >>
  `off' < type_slot_size tv` by
    metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `w2n k + off' < dimword(:256) /\ w2n k+j < dimword(:256)` by decide_tac >>
  gvs[n2w_11, LESS_MOD] >> metis_tac[]
QED
Finalise store_copy_fold_stor_taint_ok


Theorem store_copy_fold_stor_taint_ok_at:
  declared_storage_region cx mid n subs = SOME (tr,(k:bytes32),tv) /\
  MEM (tr,k,tv) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword(:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v off m) /\
  store_copy_normalize s u =
    FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
      (mload (off+32*i) s) q) s ks /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta i. key_update ta (k+n2w i)
      (mem_word_taint tn.t_mem (off+32*i)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans) /\
  tf.t_imm = tn.t_imm /\ (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_call_ctx.cc_address = cx.txn.target /\
  stor_taint_ok_at D tn s /\ dead_lo_ok H D lo cenv cx /\
  u.vs_immutables = s.vs_immutables ==>
  stor_taint_ok_at D tf u
Proof
  strip_tac >>
  `stor_taint_ok H cx (tn with t_imm := {}) s` by
    fs[bodyPtrDefsTheory.stor_taint_ok_def,
       bodyPtrDefsTheory.stor_taint_ok_at_def, bodyPtrDefsTheory.dead_lo_ok_def] >>
  `stor_taint_ok H cx (tf with t_imm := {}) u` by
    (irule store_copy_fold_stor_taint_ok >> simp[] >>
     qexistsl_tac [`k`,`ks`,`mid`,`n`,`off`,`s`,`subs`,
       `tn with t_imm := {}`,`tr`,`tv`,`v`,`writes`] >> simp[]) >>
  fs[bodyPtrDefsTheory.stor_taint_ok_def,
     bodyPtrDefsTheory.stor_taint_ok_at_def, bodyPtrDefsTheory.dead_lo_ok_def] >>
  metis_tac[]
QED

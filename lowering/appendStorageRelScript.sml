(* Live-byte agreement for a primitive storage Append. *)
Theory appendStorageRel
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs
  accountsRelProps vyperStorageFrame compileEnv loweringStateRelDefs
  vyperValue vyperStorageBackend vyperStorage words vfmState venomState
   exprLoweringProps varsExt stateFrame finite_map storageCopyLive
  vyperStorageFootprint

Theorem append_dead_bytes_word[local]:
  type_slot_size tv = 1 ==> ~dead_bytes st bs tv j b
Proof
  strip_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem append_dynamic_dead_bytes[local]:
  type_slot_size tv = 1 ==>
  ~dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b
Proof
  simp[dead_bytes_def, append_dead_bytes_word]
QED

Theorem append_root_dead_mono[local]:
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\
  len < cap /\ w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  j <> w2n (slot + n2w (1+len)) /\
  dead_bytes st (w2n slot) (ArrayTV tv (Dynamic cap)) j b ==>
  dead_bytes (update_storage slot (n2w (len+1))
    (update_storage (slot+n2w (1+len)) w st))
    (w2n slot) (ArrayTV tv (Dynamic cap)) j b
Proof
  simp[append_dynamic_dead_bytes]
QED

Theorem append_other_region_frame[local]:
  ranges_disjoint bs sz (w2n slot) (1+cap) /\
  bs + sz <= dimword (:256) /\
  w2n slot + (1+cap) <= dimword (:256) /\ len < cap /\
  type_slot_size tv = sz ==>
  (dead_bytes (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)) bs tv j b <=>
   dead_bytes st bs tv j b)
Proof
  strip_tac >> irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  `w2n (slot+n2w (1+len)) = w2n slot + (1+len)` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
         arithmeticTheory.LESS_MOD] >>
  `i < dimword (:256) /\ i <> w2n slot /\
   i <> w2n (slot+n2w (1+len))` by
    (gvs[ranges_disjoint_def] >> decide_tac) >>
  `(n2w i:bytes32) <> slot /\ n2w i <> slot+n2w (1+len)` by
    (metis_tac[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  gvs[arithmeticTheory.ADD_COMM] >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM,
       EQ_SYM_EQ]
QED

Theorem append_storage_dead_mono:
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  j <> w2n slot /\ j <> w2n (slot+n2w (1+len)) /\
  storage_dead H tr st j b ==>
  storage_dead H tr
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)) j b
Proof
  strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [storage_dead_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `other` (qx_choose_then `otv` strip_assume_tac))) >>
  pure_rewrite_tac [storage_dead_def] >>
  conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`other`, `otv`] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  Cases_on `(other,otv) = (slot,ArrayTV tv (Dynamic cap))`
  >- (qpat_x_assum `(other,otv) = _` mp_tac >>
      pure_rewrite_tac [pairTheory.PAIR_EQ] >>
      disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
      irule append_root_dead_mono >> asm_rewrite_tac []) >>
  `ranges_disjoint (w2n other) (type_slot_size otv) (w2n slot) (1+cap)` by
    (qpat_x_assum `!slot' tv'. _`
       (qspecl_then [`slot`, `ArrayTV tv (Dynamic cap)`] mp_tac) >>
     simp[type_slot_size_def]) >>
  `w2n slot + (1+cap) <= dimword (:256)` by
    gvs[ranges_disjoint_def] >>
  drule append_other_region_frame >>
  disch_then (qspecl_then [`w`, `otv`, `st`, `len`] mp_tac) >>
  asm_rewrite_tac [] >>
  disch_then (qspecl_then [`j`, `b`] mp_tac) >>
  asm_rewrite_tac []
QED

Theorem append_storage_agree:
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  storage_agree (storage_dead H tr st) st mt ==>
  storage_agree
    (storage_dead H tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)))
    (update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w st))
    (update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w mt))
Proof
  strip_tac >> pure_rewrite_tac [storage_agree_def] >> rpt strip_tac >>
  Cases_on `k = slot`
  >- gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `k = slot+n2w (1+len)`
  >- gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  `w2n k <> w2n slot /\ w2n k <> w2n (slot+n2w (1+len))` by
    metis_tac[wordsTheory.w2n_11] >>
  `~storage_dead H tr st (w2n k) b` by
    (strip_tac >> drule_all append_storage_dead_mono >> metis_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  pure_rewrite_tac [storage_agree_def] >>
  disch_then (qspecl_then [`k`, `b`] mp_tac) >>
  qpat_x_assum `len = _` kall_tac >>
  asm_simp_tac bool_ss [lookup_storage_def, update_storage_def,
      combinTheory.APPLY_UPDATE_THM, EQ_SYM_EQ]
QED

Theorem accounts_rel_append_storage_word:
  accounts_rel H cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap ==>
  accounts_rel H cx
    (set_storage cx es tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es tr))))
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  strip_tac >> Cases_on `tr` >> simp[]
  >- (irule accounts_rel_set_transient >>
      qexistsl [`es`, `s`,
        `update_storage slot (n2w (len+1))
          (update_storage (slot+n2w (1+len)) w (get_storage cx es T))`,
        `update_storage slot (n2w (len+1))
          (update_storage (slot+n2w (1+len)) w (contract_transient s))`] >>
      simp[set_storage_backend_eq, tstore_def, contract_transient_def,
           combinTheory.APPLY_UPDATE_THM] >>
      `storage_agree (storage_dead H T (get_storage cx es T))
        (get_storage cx es T) (s.vs_transient cx.txn.target)` by
        gvs[get_storage_def, accounts_rel_def, transient_agree_def] >>
      drule_all append_storage_agree >>
      disch_then (qspec_then `w` mp_tac) >>
      asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM]) >>
  irule accounts_rel_set_storage >>
  qexistsl [`es`, `s`,
    `update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es F))`,
    `update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (contract_storage s))`] >>
  simp[set_storage_backend_eq, sstore_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  `storage_agree (storage_dead H F (get_storage cx es F))
    (get_storage cx es F) (s.vs_accounts cx.txn.target).storage` by
    gvs[get_storage_def, accounts_rel_def, accounts_agree_def,
        vfmStateTheory.lookup_account_def] >>
  drule_all append_storage_agree >>
  disch_then (qspec_then `w` mp_tac) >>
  asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM]
QED

Theorem stmt_state_rel_append_storage_updates:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx es tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es tr))))
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel H cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx _ _ _ es1 s1` >>
  `accounts_rel H cx es1 s1` by
    (drule_all accounts_rel_append_storage_word >>
     disch_then (qspec_then `w` mp_tac) >>
     asm_simp_tac bool_ss [Abbr `es1`, Abbr `s1`]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel H func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`] >>
     fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def, LET_THM,
        set_storage_def, local_ptrs_rel_def, local_backed_def,
        local_region_def, lookup_var_def, immutables_rel_def,
        logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, sstore_def, tstore_def, LET_THM,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]
QED

Theorem stmt_state_rel_append_storage_word:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (res, es') ==>
  res = INL () /\
  stmt_state_rel H ctx func cenv cx es'
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  strip_tac >>
  drule_all stmt_state_rel_append_storage_updates >>
  disch_then (qspec_then `w` assume_tac) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all append_storage_word_success >> strip_tac >> gvs[] >>
  `!st1 st2. set_storage cx (set_storage cx es tr st1) tr st2 =
    set_storage cx es tr st2` by
    (Cases_on `tr` >> simp[set_storage_def, update_account_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]) >>
  asm_rewrite_tac []
QED

(* Operand preservation includes every previously bound variable; the frame
   then identifies the remaining state fields. *)
Theorem stmt_state_rel_operand_frame:
  stmt_state_rel H ctx func cenv cx es s /\
  state_frame t = state_frame s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  stmt_state_rel H ctx func cenv cx es t
Proof
  strip_tac >> irule stmt_state_rel_vars_ext >> qexists_tac `s` >>
  simp[vars_ext_def] >> conj_tac
  >- (simp[SUBMAP_FLOOKUP_EQN] >> rpt strip_tac >>
      first_x_assum (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def, lookup_var_def]) >>
  metis_tac[state_frame_eq_reconstruct]
QED

(* Growing the root header exposes just one additional child interval. *)
Theorem append_root_copy_dead_mono[local]:
  !tv cap bs len st st' j b.
    bs + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    len = w2n (lookup_storage (n2w bs) st) /\ len < cap /\
    lookup_storage (n2w bs) st' = n2w (len+1) /\
    len+1 < dimword (:256) /\
    (!x. x < dimword (:256) /\ bs < x /\
         ~(bs+1+len*type_slot_size tv <= x /\
           x < bs+1+len*type_slot_size tv+type_slot_size tv) ==>
         lookup_storage (n2w x) st' = lookup_storage (n2w x) st) /\
    ~(bs+1+len*type_slot_size tv <= j /\
      j < bs+1+len*type_slot_size tv+type_slot_size tv) /\
    dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b ==>
    dead_bytes st' bs (ArrayTV tv (Dynamic cap)) j b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `len = _` (fn th =>
    qpat_x_assum `dead_bytes _ _ _ _ _`
      (mp_tac o REWRITE_RULE [dead_bytes_def, GSYM th])) >> strip_tac >>
  pure_rewrite_tac [dead_bytes_def] >>
  qexists_tac `i` >> asm_simp_tac bool_ss [w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `i <> len` by
    (strip_tac >> gvs[] >> drule (cj 1 dead_bytes_range) >> decide_tac) >>
  `i * type_slot_size tv + type_slot_size tv <= len * type_slot_size tv \/
   len * type_slot_size tv + type_slot_size tv <= i * type_slot_size tv` by
    (Cases_on `i < len`
     >- metis_tac[vyperLookupStorageTheory.array_index_element_end_bound] >>
     `len < i` by decide_tac >>
     metis_tac[vyperLookupStorageTheory.array_index_element_end_bound]) >>
  `i * type_slot_size tv + type_slot_size tv <= cap * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `dead_bytes st' (bs+1+i*type_slot_size tv) tv j b <=>
   dead_bytes st (bs+1+i*type_slot_size tv) tv j b` suffices_by simp[] >>
  irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  first_x_assum irule >>
  qpat_x_assum `bs + type_slot_size _ <= _` mp_tac >>
  pure_rewrite_tac [type_slot_size_def] >> decide_tac
QED

Theorem append_storage_copy_dead_mono[local]:
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  len = w2n (lookup_storage slot st) /\ len < cap /\
  len+1 < dimword (:256) /\
  lookup_storage slot st' = n2w (len+1) /\
  (!x. x < dimword (:256) /\ x <> w2n slot /\
       ~(w2n slot+1+len*type_slot_size tv <= x /\
         x < w2n slot+1+len*type_slot_size tv+type_slot_size tv) ==>
       lookup_storage (n2w x) st' = lookup_storage (n2w x) st) /\
  ~(w2n slot+1+len*type_slot_size tv <= j /\
    j < w2n slot+1+len*type_slot_size tv+type_slot_size tv) /\
  storage_dead H tr st j b ==>
  storage_dead H tr st' j b
Proof
  strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [storage_dead_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `other` (qx_choose_then `otv` strip_assume_tac))) >>
  pure_rewrite_tac [storage_dead_def] >>
  conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`other`, `otv`] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- asm_rewrite_tac [] >>
  Cases_on `(other,otv) = (slot,ArrayTV tv (Dynamic cap))`
  >- (qpat_x_assum `(other,otv) = _`
        (fn th => map_every SUBST_ALL_TAC (CONJUNCTS (REWRITE_RULE [pairTheory.PAIR_EQ] th))) >>
      irule append_root_copy_dead_mono >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`len`, `st`] >> asm_simp_tac bool_ss [n2w_w2n] >>
      rpt strip_tac >> simp[] >> gvs[]) >>
  `ranges_disjoint (w2n other) (type_slot_size otv)
      (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))` by
    (qpat_x_assum `!slot' tv'. _`
       (qspecl_then [`slot`, `ArrayTV tv (Dynamic cap)`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac [] >> strip_tac >> gvs[]) >>
     simp[]) >>
  `len*type_slot_size tv + type_slot_size tv <= cap*type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `dead_bytes st' (w2n other) otv j b <=> dead_bytes st (w2n other) otv j b`
    suffices_by simp[] >>
  irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  first_x_assum irule >> fs[ranges_disjoint_def, type_slot_size_def] >> gvs[]
QED

Theorem append_copy_layout[local]:
  !(slot:bytes32) tv cap len.
    w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    0 < type_slot_size tv /\ len < cap ==>
    w2n (slot+n2w (1+len*type_slot_size tv)) = w2n slot+1+len*type_slot_size tv /\
    w2n (slot+n2w (1+len*type_slot_size tv))+type_slot_size tv <= dimword (:256) /\
    len+1 < dimword (:256)
Proof
  rpt strip_tac >>
  `len*type_slot_size tv+type_slot_size tv <= cap*type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `len+1 <= cap*type_slot_size tv` by
    (`len+1 <= (len+1)*type_slot_size tv` by simp[] >>
     pop_assum mp_tac >>
     pure_rewrite_tac [arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `w2n slot+1+len*type_slot_size tv < dimword (:256)` by
    (fs[type_slot_size_def] >> decide_tac) >>
  `w2n (slot+n2w (1+len*type_slot_size tv)) = w2n slot+1+len*type_slot_size tv` by
    simp[wordsTheory.word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  fs[type_slot_size_def] >> decide_tac
QED

Theorem append_copy_source_outside[local]:
  !tv v writes k slot st len x.
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    x < dimword (:256) /\ x <> w2n slot /\
    ~(w2n k <= x /\ x < w2n k+type_slot_size tv) ==>
    lookup_storage (n2w x)
      (update_storage slot (n2w (len+1)) (apply_writes k writes st)) =
    lookup_storage (n2w x) st
Proof
  rpt strip_tac >>
  `(n2w x:bytes32) <> slot` by
    (strip_tac >> gvs[w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `lookup_storage (n2w x) (update_storage slot (n2w (len+1)) (apply_writes k writes st)) =
   lookup_storage (n2w x) (apply_writes k writes st)` by
    simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM, EQ_SYM_EQ] >>
  pop_assum SUBST1_TAC >>
  irule copy_encoded_outside >> metis_tac[]
QED

Theorem append_storage_agree_copy:
  !H tr slot tv cap len k v writes off mem st mt.
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    (!slot' tv'.
      MEM (tr,slot',tv') (FST H) /\
      (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
      ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
        (w2n slot') (type_slot_size tv')) /\
    0 < type_slot_size tv /\ len = w2n (lookup_storage slot st) /\ len < cap /\
    k = slot+n2w (1+len*type_slot_size tv) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\ val_in_memory tv v off mem /\
    (!i b. i < type_slot_size tv /\ b < 32 /\
      ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+i) b ==>
      MEM i (MAP FST writes)) /\
    storage_agree (storage_dead H tr st) st mt ==>
    storage_agree
      (storage_dead H tr (update_storage slot (n2w (len+1)) (apply_writes k writes st)))
      (update_storage slot (n2w (len+1)) (apply_writes k writes st))
      (update_storage slot (n2w (len+1))
        (FOLDL (\t i. update_storage (k+n2w i) (mem_word_at (off+32*i) mem) t)
          mt (COUNT_LIST (type_slot_size tv))))
Proof
  rpt gen_tac >> strip_tac >>
  `w2n k = w2n slot+1+len*type_slot_size tv /\
   w2n k+type_slot_size tv <= dimword (:256) /\ len+1 < dimword (:256)` by
    (qpat_x_assum `k = _` SUBST1_TAC >> drule_all append_copy_layout >> simp[]) >>
  qmatch_goalsub_abbrev_tac `storage_dead H tr st'` >>
  `lookup_storage slot st' = n2w (len+1)` by
    simp[Abbr `st'`, lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  `!x. x < dimword (:256) /\ x <> w2n slot /\
       ~(w2n k <= x /\ x < w2n k+type_slot_size tv) ==>
       lookup_storage (n2w x) st' = lookup_storage (n2w x) st` by
    (rpt strip_tac >> simp_tac bool_ss [Abbr `st'`] >>
     irule append_copy_source_outside >> metis_tac[]) >>
  pure_rewrite_tac [storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead H tr st' (w2n q) b` >>
  Cases_on `q = slot`
  >- gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  `w2n q <> w2n slot` by metis_tac[w2n_11] >>
  `lookup_storage q
    (update_storage slot (n2w (len+1))
      (FOLDL (\t i. update_storage (k+n2w i) (mem_word_at (off+32*i) mem) t)
        mt (COUNT_LIST (type_slot_size tv)))) =
   if w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv then
     mem_word_at (off+32*(w2n q-w2n k)) mem else lookup_storage q mt` by
    (`!t. lookup_storage q (update_storage slot (n2w (len+1)) t) = lookup_storage q t` by
       simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM, EQ_SYM_EQ] >>
     asm_rewrite_tac[] >> gvs[copy_fold_region]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv` >> asm_rewrite_tac[]
  >- suspend "child" >> suspend "outside"
QED
Resume append_storage_agree_copy[child]:
  `len*type_slot_size tv + type_slot_size tv <= cap*type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `~tr \/ ~MEM (w2n q) (SND H)` by
    (Cases_on `tr` >> asm_rewrite_tac [] >> strip_tac >>
     qpat_x_assum `storage_locks_separated _ _` mp_tac >>
     simp[storage_locks_separated_def] >>
     qexistsl_tac [`slot`, `ArrayTV tv (Dynamic cap)`, `w2n q`] >>
     fs[ranges_disjoint_def, type_slot_size_def]) >>
  `~dead_bytes st' (w2n slot) (ArrayTV tv (Dynamic cap)) (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [storage_dead_def] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`slot`, `ArrayTV tv (Dynamic cap)`] >>
     asm_rewrite_tac[]) >>
  `~dead_bytes st' (w2n k) tv (w2n q) b` by
    (strip_tac >>
     qpat_x_assum `~dead_bytes st' _ (ArrayTV _ _) _ _` mp_tac >>
     pure_rewrite_tac [dead_bytes_def] >> simp_tac bool_ss [] >>
     qexists_tac `len` >>
     asm_simp_tac bool_ss [n2w_w2n, w2n_n2w, arithmeticTheory.LESS_MOD] >>
     gvs[]) >>
  `dead_bytes st' (w2n k) tv (w2n q) b <=>
   dead_bytes (apply_writes k writes st) (w2n k) tv (w2n q) b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     `i < dimword (:256)` by decide_tac >>
     `w2n slot < w2n k` by
       (qpat_x_assum `w2n k = _` SUBST1_TAC >> simp[]) >>
     `i <> w2n slot` by decide_tac >>
     `(n2w i:bytes32) <> slot` by
       (strip_tac >> qpat_x_assum `n2w i = slot`
          (mp_tac o AP_TERM ``w2n:bytes32->num``) >>
        asm_simp_tac bool_ss [w2n_n2w, arithmeticTheory.LESS_MOD]) >>
     simp[Abbr `st'`, lookup_storage_def, update_storage_def,
          combinTheory.APPLY_UPDATE_THM, EQ_SYM_EQ]) >>
  `lookup_storage q st' = lookup_storage q (apply_writes k writes st)` by
    simp[Abbr `st'`, lookup_storage_def, update_storage_def,
         combinTheory.APPLY_UPDATE_THM, EQ_SYM_EQ] >>
  `w2n k+(w2n q-w2n k) = w2n q /\ w2n q-w2n k < type_slot_size tv` by decide_tac >>
  `MEM (w2n q-w2n k) (MAP FST writes)` by
    (first_x_assum irule >> simp[] >> qexists_tac `b` >> gvs[]) >>
  `~dead_bytes (apply_writes k writes st) (w2n k) tv
     (w2n k+(w2n q-w2n k)) b` by gvs[] >>
  drule_all encode_value_memory_live >> simp[]
QED
Resume append_storage_agree_copy[outside]:
  `~storage_dead H tr st (w2n q) b` by
    (strip_tac >>
     `storage_dead H tr st' (w2n q) b` suffices_by metis_tac[] >>
     irule append_storage_copy_dead_mono >>
     metis_tac[]) >>
  `lookup_storage q st' = lookup_storage q st` by
    (qpat_x_assum `!x. _ ==> lookup_storage _ st' = _` (qspec_then `w2n q` mp_tac) >>
     gvs[w2n_lt]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >> simp[storage_agree_def]
QED
Finalise append_storage_agree_copy


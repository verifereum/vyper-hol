(* Live-byte agreement for a primitive storage Append. *)
Theory appendStorageRel
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimAppendStorage accountsRelProps vyperStorageFrame compileEnv loweringStateRelDefs
  vyperValue vyperStorageBackend vyperStorage words vfmState venomState
   exprLoweringProps  varsExt stateFrame finite_map

Theorem append_dead_bytes_word[local]:
  type_slot_size tv = 1 ==> ~dead_bytes st bs tv j b
Proof
  strip_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem append_dynamic_dead_bytes[local]:
  type_slot_size tv = 1 ==>
  (dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b <=>
   bs + 1 + w2n (lookup_storage (n2w bs) st) <= j /\
   j < bs + 1 + cap /\ b < 32)
Proof
  strip_tac >> pure_rewrite_tac [dead_bytes_def] >>
  eq_tac
  >- (strip_tac >> rename1 `i < cap` >>
      Cases_on `i < w2n (lookup_storage (n2w bs) st)` >>
      gvs[append_dead_bytes_word] >> decide_tac) >>
  strip_tac >> qexists_tac `j - (bs+1)` >>
  `~(j - (bs+1) < w2n (lookup_storage (n2w bs) st))` by decide_tac >>
  simp[] >> decide_tac
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
  strip_tac >>
  `len + 1 < dimword (:256) /\ w2n slot + (1+len) < dimword (:256)` by
    (gvs[type_slot_size_def] >> decide_tac) >>
  `w2n (slot + n2w (1+len)) = w2n slot + (1+len)` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
         arithmeticTheory.LESS_MOD] >>
  gvs[append_dynamic_dead_bytes, lookup_storage_def, update_storage_def,
      combinTheory.APPLY_UPDATE_THM, wordsTheory.w2n_n2w,
      arithmeticTheory.LESS_MOD] >> decide_tac
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
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  j <> w2n slot /\ j <> w2n (slot+n2w (1+len)) /\
  storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)) j b
Proof
  strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [storage_dead_def]) >>
  rename1 `dead_bytes st (w2n other) otv j b` >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by
    (Cases_on `(other,otv) = (slot,ArrayTV tv (Dynamic cap))` >- gvs[] >>
     qpat_x_assum `!mid' n' subs' slot' tv'. _`
       (qspecl_then [`mid`, `n`, `[]`, `slot`, `ArrayTV tv (Dynamic cap)`] mp_tac) >>
     simp[ranges_disjoint_def]) >>
  pure_rewrite_tac [storage_dead_def] >>
  qexistsl_tac [`mid'`, `n'`, `subs`, `other`, `otv`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `(other,otv) = (slot,ArrayTV tv (Dynamic cap))`
  >- (gvs[] >> qpat_x_assum `!mid'' n'' subs' slot' tv'. _` kall_tac >>
      metis_tac[append_root_dead_mono, arithmeticTheory.ADD_COMM]) >>
  `ranges_disjoint (w2n other) (type_slot_size otv) (w2n slot) (1+cap)` by
    (qpat_x_assum `!mid' n' subs' slot' tv'. _`
       (qspecl_then [`mid`, `n`, `[]`, `slot`, `ArrayTV tv (Dynamic cap)`] mp_tac) >>
     simp[type_slot_size_def]) >>
  `w2n slot + (1+cap) <= dimword (:256)` by gvs[type_slot_size_def] >>
  drule append_other_region_frame >>
  disch_then (qspecl_then [`w`, `otv`, `st`, `len`] mp_tac) >>
  asm_rewrite_tac [] >> disch_then (qspecl_then [`j`, `b`] mp_tac) >>
  asm_rewrite_tac []
QED

Theorem append_storage_agree:
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  storage_agree (storage_dead cx tr st) st mt ==>
  storage_agree
    (storage_dead cx tr (update_storage slot (n2w (len+1))
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
  `~storage_dead cx tr st (w2n k) b` by
    (strip_tac >> drule_all append_storage_dead_mono >> metis_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  pure_rewrite_tac [storage_agree_def] >>
  disch_then (qspecl_then [`k`, `b`] mp_tac) >>
  qpat_x_assum `len = _` kall_tac >>
  asm_simp_tac bool_ss [lookup_storage_def, update_storage_def,
      combinTheory.APPLY_UPDATE_THM, EQ_SYM_EQ]
QED

Theorem accounts_rel_append_storage_word:
  accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap ==>
  accounts_rel cx
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
      `storage_agree (storage_dead cx T (get_storage cx es T))
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
  `storage_agree (storage_dead cx F (get_storage cx es F))
    (get_storage cx es F) (s.vs_accounts cx.txn.target).storage` by
    gvs[get_storage_def, accounts_rel_def, accounts_agree_def,
        vfmStateTheory.lookup_account_def] >>
  drule_all append_storage_agree >>
  disch_then (qspec_then `w` mp_tac) >>
  asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM]
QED

Theorem stmt_state_rel_append_storage_updates:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es tr))))
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx _ _ _ es1 s1` >>
  `accounts_rel cx es1 s1` by
    (drule_all accounts_rel_append_storage_word >>
     disch_then (qspec_then `w` mp_tac) >>
     asm_simp_tac bool_ss [Abbr `es1`, Abbr `s1`]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
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
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (res, es') ==>
  res = INL () /\
  stmt_state_rel ctx func cenv cx es'
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
  stmt_state_rel ctx func cenv cx es s /\
  state_frame t = state_frame s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >> irule stmt_state_rel_vars_ext >> qexists_tac `s` >>
  simp[vars_ext_def] >> conj_tac
  >- (simp[SUBMAP_FLOOKUP_EQN] >> rpt strip_tac >>
      first_x_assum (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def, lookup_var_def]) >>
  metis_tac[state_frame_eq_reconstruct]
QED

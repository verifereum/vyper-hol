(* A primitive Append changes only its resolved storage subregion. *)
Theory appendResolvedStorageRel
Ancestors
  placeStoreStorage accountsRelProps loweringStateRelDefs
  exprSimProps stmtSimProps loweringPosts stateFrame
  vyperStoragePlaceRegion vyperStorage vyperStorageBackend
  venomState vfmState words combin

Theorem append_resolved_storage_dead_mono:
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap /\
  storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)) j b
Proof
  strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n slot + (1+cap) <= dimword (:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (slot+n2w (1+len)) = w2n slot + (1+len)` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
         arithmeticTheory.LESS_MOD] >>
  `!bs. ~dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b` by
    (rpt gen_tac >> strip_tac >>
     pop_assum (strip_assume_tac o PURE_ONCE_REWRITE_RULE [dead_bytes_def]) >>
     drule (cj 1 dead_bytes_range) >> simp[]) >>
  `storage_read_live cx tr st slot (ArrayTV tv (Dynamic cap))` by
    (irule storage_subregion_read_live >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[declared_storage_region_read_live]) >>
  `~(w2n rootk + delta <= j /\
      j < w2n rootk + delta + type_slot_size (ArrayTV tv (Dynamic cap)))` by
    (qpat_x_assum `storage_read_live _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [storage_read_live_def]) >>
     disch_then (qspecl_then [`j`, `b`] mp_tac) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  irule place_store_storage_dead_subregion_frame >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`mid`, `name`, `path`, `root`, `st`, `subs`] >>
  simp[vyperValueTheory.type_slot_size_def] >> rpt strip_tac >>
  `q <> slot /\ q <> slot+n2w (1+len)` by
    (rpt strip_tac >> gvs[] >> decide_tac) >>
  qpat_x_assum `q <> slot+n2w (1+len)`
    (mp_tac o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM, EQ_SYM_EQ]
QED

Theorem append_resolved_storage_agree:
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap /\
  storage_agree (storage_dead cx tr st) st mt ==>
  storage_agree
    (storage_dead cx tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)))
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st))
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w mt))
Proof
  strip_tac >> pure_rewrite_tac [storage_agree_def] >> rpt strip_tac >>
  Cases_on `k = slot`
  >- gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  Cases_on `k = slot+n2w (1+len)`
  >- gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  `~storage_dead cx tr st (w2n k) b` by
    (strip_tac >> drule_all append_resolved_storage_dead_mono >> metis_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  pure_rewrite_tac [storage_agree_def] >>
  disch_then (qspecl_then [`k`, `b`] mp_tac) >>
  asm_simp_tac bool_ss [lookup_storage_def, update_storage_def,
                       APPLY_UPDATE_THM, EQ_SYM_EQ]
QED

Theorem stmt_state_rel_append_resolved_storage_updates:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es tr))))
    (if tr then tstore slot (n2w (len+1))
      (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1))
      (sstore (slot+n2w (1+len)) w s))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx _ _ _ es1 s1` >>
  `accounts_rel cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`]
     >- (irule accounts_rel_set_transient >>
         qexistsl_tac [`es`, `s`,
           `update_storage slot (n2w (len+1))
             (update_storage (slot+n2w (1+len)) w (get_storage cx es T))`,
           `update_storage slot (n2w (len+1))
             (update_storage (slot+n2w (1+len)) w (contract_transient s))`] >>
         simp[set_storage_backend_eq, tstore_def, contract_transient_def,
              APPLY_UPDATE_THM] >>
         `storage_agree (storage_dead cx T (get_storage cx es T))
           (get_storage cx es T) (s.vs_transient cx.txn.target)` by
           gvs[get_storage_def, accounts_rel_def, transient_agree_def] >>
         `w2n slot = w2n rootk + delta /\
          w2n rootk + type_slot_size root <= dimword (:256)` by decide_tac >>
     drule_all append_resolved_storage_agree >>
         disch_then (qspec_then `w` mp_tac) >>
         asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM]) >>
     irule accounts_rel_set_storage >>
     qexistsl_tac [`es`, `s`,
       `update_storage slot (n2w (len+1))
         (update_storage (slot+n2w (1+len)) w (get_storage cx es F))`,
       `update_storage slot (n2w (len+1))
         (update_storage (slot+n2w (1+len)) w (contract_storage s))`] >>
     simp[set_storage_backend_eq, sstore_def, contract_storage_def,
          lookup_account_def, APPLY_UPDATE_THM] >>
     `storage_agree (storage_dead cx F (get_storage cx es F))
       (get_storage cx es F) (s.vs_accounts cx.txn.target).storage` by
       gvs[get_storage_def, accounts_rel_def, accounts_agree_def,
           lookup_account_def] >>
     `w2n slot = w2n rootk + delta /\
          w2n rootk + type_slot_size root <= dimword (:256)` by decide_tac >>
     drule_all append_resolved_storage_agree >>
     disch_then (qspec_then `w` mp_tac) >>
     asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`] >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, sstore_def, tstore_def, LET_THM,
        set_storage_def, local_ptrs_rel_def, local_backed_def,
        local_region_def, lookup_var_def, immutables_rel_def,
        logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     irule exprLoweringPropsTheory.immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, sstore_def, tstore_def, LET_THM,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     irule exprLoweringPropsTheory.immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM, lookup_var_def]) >>
  irule exprLoweringPropsTheory.stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]
QED

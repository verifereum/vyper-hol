(* State bridges for memory-to-storage copy and normalization. *)
Theory stmtSimStoreCopyState
Ancestors
  stmtSimStoreCopy exprSimProps exprLoweringProps accountsRelProps
  compileEnv loweringStateRelDefs loweringPosts vyperStorageBackend
  vfmState venomState venomMemDefs valueEncoding
  list rich_list arithmetic words

Theorem stmt_state_selected_storage_agree:
 !ctx func cenv cx es s tr.
 stmt_state_rel ctx func cenv cx es s ==>
 storage_agree (storage_dead cx tr (get_storage cx es tr))
   (get_storage cx es tr)
   (if tr then contract_transient s else contract_storage s)
Proof
 rpt gen_tac >> strip_tac >> Cases_on `tr` >>
 gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
     get_storage_def, lookup_account_def]
QED

Theorem stmt_state_storage_patch:
 !ctx func cenv cx es s tr stor backend.
 stmt_state_rel ctx func cenv cx es s /\
 storage_agree (storage_dead cx tr stor) stor backend ==>
 stmt_state_rel ctx func cenv cx (set_storage cx es tr stor)
   (if tr then s with vs_transient :=
       (s.vs_call_ctx.cc_address =+ backend) s.vs_transient
    else s with vs_accounts :=
       (s.vs_call_ctx.cc_address =+
          (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage := backend))
        s.vs_accounts)
Proof
 rpt gen_tac >> strip_tac >>
 `s.vs_call_ctx.cc_address = cx.txn.target` by
   fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
 qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx es' s'` >>
 `accounts_rel cx es' s'` by
   (Cases_on `tr`
    >- (irule accounts_rel_set_transient >>
        qexistsl_tac [`es`, `s`, `stor`, `backend`] >>
        fs[stmt_state_rel_def, state_rel_def, Abbr `es'`, Abbr `s'`,
           set_storage_backend_eq]) >>
    irule accounts_rel_set_storage >>
    qexistsl_tac [`es`, `s`, `stor`, `backend`] >>
    fs[stmt_state_rel_def, state_rel_def, Abbr `es'`, Abbr `s'`,
       set_storage_backend_eq]) >>
 fs[stmt_state_rel_def, state_rel_def] >>
 Cases_on `tr` >>
 fs[Abbr `es'`, Abbr `s'`] >>
 (conj_tac
  >- (conj_tac
      >- (qpat_assum `local_ptrs_rel _ _ _ s` mp_tac >>
          simp_tac (boss_ss()) [local_ptrs_rel_def, local_backed_def,
                               local_region_def, lookup_var_def]) >>
      conj_tac
      >- fs[storage_rel_def, set_storage_def, contract_storage_def,
            lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
      conj_tac
      >- fs[transient_rel_def, set_storage_def, contract_transient_def,
            combinTheory.APPLY_UPDATE_THM] >>
      conj_tac
      >- (qpat_assum `immutables_rel _ _ _ _ _ s` mp_tac >>
          simp_tac (boss_ss()) [immutables_rel_def, set_storage_def]) >>
      conj_tac
      >- (qpat_assum `logs_rel _ _ _ s` mp_tac >>
          simp_tac (boss_ss()) [logs_rel_def, set_storage_def]) >>
      simp[set_storage_def]) >>
  conj_tac
  >- (qpat_assum `alloca_inv s` mp_tac >>
      simp_tac (boss_ss()) [alloca_inv_def, allocas_non_overlapping_def,
                           alloca_next_valid_def]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac
  >- (irule fmp_room_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac
  >- (qpat_assum `immutable_alloca_sep _ _ _ _ s` mp_tac >>
      simp_tac (boss_ss()) [immutable_alloca_sep_def, immutable_decl_sep_def, set_storage_def,
                           local_region_def, lookup_var_def]) >>
  conj_tac
  >- (qpat_assum `immutable_base_zero _ s` mp_tac >>
      simp_tac (boss_ss()) [immutable_base_zero_def, oneline eval_operand_def,
                           lookup_var_def]) >>
  first_assum ACCEPT_TAC)
QED

Theorem place_store_normalize_state:
  stmt_state_rel ctx func cenv cx es (store_copy_normalize q t) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x q) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
    ((store_copy_normalize q t) with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         first_x_assum drule >> simp[store_copy_normalize_def, lookup_var_def]) >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         first_x_assum drule >> simp[store_copy_normalize_def, lookup_var_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (store_copy_normalize _ _)` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac (srw_ss()) [store_copy_normalize_def, stmt_state_rel_def, state_rel_def,
    local_ptrs_rel_def, local_region_def, local_backed_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
    venomMemDefsTheory.alloca_inv_def, alloca_room_def, fmp_room_def,
    immutable_alloca_sep_def, immutable_decl_sep_def, immutable_base_zero_def,
    lookup_var_def, oneline eval_operand_def, contract_storage_def, contract_transient_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, pending_alloca_size_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem place_store_prefix_backend_natural:
  !tr. w2n b + 32*i <= dimword (:256) ==>
  (if tr then contract_transient else contract_storage)
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s i) =
  FOLDL (\t h. update_storage (k+n2w h)
          (mem_word_at (32*h+w2n b) s.vs_memory) t)
    ((if tr then contract_transient else contract_storage) s) (COUNT_LIST i)
Proof
  gen_tac >> strip_tac >> rewrite_tac[place_store_prefix_backend] >>
  irule FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  rename1 `h < i` >>
  `w2n b + 32*h < dimword (:256)` by decide_tac >>
  `b+n2w h*32w = n2w (w2n b+32*h)` by
    (rewrite_tac[word_mul_n2w] >>
     pure_rewrite_tac[GSYM word_add_n2w, n2w_w2n] >>
     simp_tac bool_ss [MULT_COMM]) >>
  simp[mload_def, valueEncodingDefsTheory.mem_word_at_def]
QED

Theorem place_store_prefix_state_patch:
  !i s b k tr.
  store_copy_prefix (if tr then LocTransient else LocStorage) b k s i =
  (if tr then s with vs_transient :=
      (s.vs_call_ctx.cc_address =+
        contract_transient (store_copy_prefix LocTransient b k s i)) s.vs_transient
   else s with vs_accounts :=
      (s.vs_call_ctx.cc_address =+
       (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
         contract_storage (store_copy_prefix LocStorage b k s i))) s.vs_accounts)
Proof
  Induct_on `i`
  >- (rpt gen_tac >> Cases_on `tr` >>
      simp[place_store_prefix_eqs, contract_transient_def, contract_storage_def,
           vfmStateTheory.lookup_account_def, combinTheory.UPDATE_def, SF ETA_ss]) >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`s`, `b`, `k`, `tr`] assume_tac) >>
  Cases_on `tr` >> gvs[] >>
  once_rewrite_tac[place_store_prefix_eqs] >>
  simp[sstore_def, tstore_def, contract_transient_def, contract_storage_def,
       place_store_prefix_fields, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  qpat_assum `store_copy_prefix _ _ _ _ _ = _`
    (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
  once_asm_rewrite_tac [] >>
  simp[contract_transient_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

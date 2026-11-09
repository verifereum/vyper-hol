Theory placeStoreStatePatch
Ancestors
  exprLoweringProps accountsRelProps compileEnv loweringStateRelDefs vyperStorageBackend
  vfmState venomState venomMemDefs

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
      simp_tac (boss_ss()) [immutable_alloca_sep_def, set_storage_def,
                           local_region_def, lookup_var_def]) >>
  conj_tac
  >- (qpat_assum `immutable_base_zero _ s` mp_tac >>
      simp_tac (boss_ss()) [immutable_base_zero_def, oneline eval_operand_def,
                           lookup_var_def]) >>
  first_assum ACCEPT_TAC)
QED

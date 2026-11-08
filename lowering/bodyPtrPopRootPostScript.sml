Theory bodyPtrPopRootPost
Ancestors
  exprSimPopStorage exprSimWordArgs exprSimLen appendStorageSourcePtr
  loweringPosts vyperState compileEnv exprLoweringProps venomState context

Theorem pop_storage_place_holds_gas_obs:
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tv)) w es s ==>
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tv)) w
    (es with gas_obs := g) s
Proof
  rw[storage_holds_def, read_result_def, read_place_def] >>
  qexistsl [`tvt`, `v`] >> simp[len_rss_obs, get_storage_gas_obs]
QED

Theorem pop_root_positive_post:
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,hdr,ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ local_ptrs_reserved cenv sa /\
  len = w2n (lookup_storage hdr (get_storage cx es tr)) /\ 0 < len /\
  elem = hdr + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore hdr (n2w (len - 1)) s
       else sstore hdr (n2w (len - 1)) s) with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) /\
  lookup_var x u = SOME elem ==>
  vv_post ctx func cenv cx (Pop ann tgt) es sa sb s
    (set_storage cx es tr
      (apply_writes hdr [(0,n2w (len - 1))] (get_storage cx es tr))
      with gas_obs := g)
    (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  irule pop_storage_vv_post >> simp[] >>
  conj_tac
  >- (simp[stmt_state_rel_gas_obs] >>
      irule pop_storage_updated_state_rel >>
      conj_tac >- metis_tac[] >> qexistsl [`s`,`sa`] >> gvs[]) >>
  irule pop_storage_place_holds_gas_obs >>
  irule pop_storage_positive_holds >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  gvs[] >> Cases_on `tr` >> gvs[]
QED

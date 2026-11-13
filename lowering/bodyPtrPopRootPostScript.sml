Theory bodyPtrPopRootPost
Ancestors
  exprSimPopStorage exprSimWordArgs exprSimLen stmtSimAppendStorageCompose
  loweringPosts vyperState compileEnv exprLoweringProps venomState context

(* The positive pop's post at the source endpoint, whose trace has recorded
   the header root and whose end storage is well formed on the horizon. *)
Theorem pop_root_positive_post:
  stmt_state_rel H ctx func cenv cx es s /\
  regions_consistent (FST H) /\ storage_well_formed_on cx es (FST H) /\
  MEM (tr,hdr,ArrayTV tv (Dynamic n)) (FST H) /\
  storage_well_formed_on cx
    (set_storage cx es tr
      (apply_writes hdr [(0,n2w (len - 1))] (get_storage cx es tr))) (FST H) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ local_ptrs_reserved cenv sa /\
  len = w2n (lookup_storage hdr (get_storage cx es tr)) /\ 0 < len /\
  elem = hdr + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore hdr (n2w (len - 1)) s
       else sstore hdr (n2w (len - 1)) s) with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) /\
  lookup_var x u = SOME elem ==>
  vv_post H ctx func cenv cx (Pop ann tgt) es sa sb s
    ((set_storage cx es tr
       (apply_writes hdr [(0,n2w (len - 1))] (get_storage cx es tr))
      with storage_trace := obs) with gas_obs := g)
    (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  qabbrev_tac `es1 = set_storage cx es tr
    (apply_writes hdr [(0,n2w (len - 1))] (get_storage cx es tr))` >>
  `stmt_state_rel H ctx func cenv cx es1 u` by
    (qunabbrev_tac `es1` >> qpat_x_assum `len = _` SUBST_ALL_TAC >>
     drule_all pop_storage_updated_state_rel >> disch_then ACCEPT_TAC) >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem es1 u` by
    (qunabbrev_tac `es1` >> irule pop_storage_positive_holds >> metis_tac[]) >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
     ((es1 with storage_trace := obs) with gas_obs := g) u` by
    (irule pop_storage_holds_end >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx
     ((es1 with storage_trace := obs) with gas_obs := g) (FST H)` by
    (`((es1 with storage_trace := obs) with gas_obs := g).accounts = es1.accounts /\
      ((es1 with storage_trace := obs) with gas_obs := g).tStorage = es1.tStorage` by
       simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `stmt_state_rel H ctx func cenv cx
     ((es1 with storage_trace := obs) with gas_obs := g) u` by simp[] >>
  `((es1 with storage_trace := obs) with gas_obs := g).scopes = es.scopes` by
    (simp[Abbr `es1`] >> Cases_on `tr` >> simp[vyperStorageBackendTheory.set_storage_def]) >>
  `!id path. PlaceR (StoragePlace tr elem tv) <> PlaceR (MemoryPlace id path)` by
    simp[] >>
  irule pop_storage_vv_post >> metis_tac[]
QED

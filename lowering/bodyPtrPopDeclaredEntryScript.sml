Theory bodyPtrPopDeclaredEntry
Ancestors
  bodyPtrPopRegionInvariant bodyPtrDefs exprLoweringProps accountsRelProps
  vyperStorageBackend venomState compileEnv loweringStateRelDefs vyperState vfmState

(* For any root the horizon observed, the source header word agrees with
   the selected backend directly, without sload/tload wrappers. *)
Theorem pop_declared_header_agree:
  MEM (tr,w,tv) (FST H) /\
  stmt_state_rel H ctx func cenv cx es s /\ 0 < type_slot_size tv ==>
  lookup_storage w (get_storage cx es tr) =
    lookup_storage w
      (if tr then s.vs_transient s.vs_call_ctx.cc_address
       else (s.vs_accounts s.vs_call_ctx.cc_address).storage)
Proof
  strip_tac >>
  `accounts_rel H cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule accounts_rel_storage_transient >>
  disch_then (drule_at Any) >> strip_tac >>
  `storage_read_live H tr (get_storage cx es tr) w tv` by
    metis_tac[observed_storage_region_read_live] >>
  `storage_agree (storage_dead H tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[storage_rel_def, transient_rel_def, get_storage_def, lookup_account_def]) >>
  drule_all storage_agree_read_head >>
  Cases_on `tr` >> simp[contract_transient_def, contract_storage_def, lookup_account_def]
QED

Theorem pop_declared_region_taint:
  MEM (tr,w : bytes32,tv) (FST H) /\
  stmt_state_rel H ctx func cenv cx es s /\ ghost_inv H d cenv cx es G tn s ==>
  pop_region_taint_ok
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (w2n w) tv (if tr then tn.t_trans else tn.t_stor)
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ stor_taint_ok H cx tn s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def, ghost_inv_def] >>
  Cases_on `tr` >> gvs[]
  >- (irule pop_region_taint_transient_entry >>
      simp[] >> metis_tac[observed_storage_region_read_live]) >>
  irule pop_region_taint_storage_entry >>
  simp[] >> metis_tac[observed_storage_region_read_live]
QED

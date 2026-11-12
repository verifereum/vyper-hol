Theory bodyPtrPopStoragePureEndpoint
Ancestors
  bodyPtrPopStoragePureCounted bodyPtrPopStoragePurePost bodyPtrPopStoragePureOutcome
  bodyPtrPopRootEndpoint bodyPtrHashBuiltinsGhostFrame exprSimPopNestedBase
  exprSimVVFrame bodyPtrDefs compileEnv loweringStateRelDefs exprLoweringProps loweringPosts
  venomState ptrDiscipline context vyperStorageBackend vyperStorage
  vyperValue list finite_map pred_set

Theorem pop_storage_positive_endpoint:
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic cap))))
    (Type (ArrayT ann (Dynamic cap))) (hdr,loc,pt) s /\
  ci_mono sa sm /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  declared_storage_region cx mid name keys = SOME (tr,root,root_tv) /\
  storage_subregion root_tv path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n root + delta /\
  storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s)
    slot (ArrayTV tv (Dynamic cap)) /\
  storage_read_live cx tr
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic cap)) /\
  slots_in_range (get_storage cx es tr) (w2n slot) (ArrayTV tv (Dynamic cap)) /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ 0 < len /\ len <= cap /\
  ee = set_storage cx es tr (apply_writes slot [(0,n2w (len-1))] (get_storage cx es tr)) /\
  u = ((if tr then tstore slot (n2w (len-1)) s
        else sstore slot (n2w (len-1)) s) with vs_vars := u.vs_vars)
        with vs_inst_idx := k /\
  eval_operand op u = SOME (slot + n2w (1 + (len-1) * type_slot_size tv)) /\
  op_taint tnf op = {} /\ EVERY (\x. ~not_fresh_at sm x) xs /\
  tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
  tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
  tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
  (!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tnf (Var x) = op_taint tn (Var x) /\ lookup_var x u = lookup_var x s) ==>
  vv_post ctx func cenv cx (Pop ann bt) es0 sa sb s0 ee
    (PlaceR (StoragePlace tr (slot + n2w (1 + (len-1) * type_slot_size tv)) tv))
    (LocatedValue ann (mk_ptr op (if tr then LocTransient else LocStorage))) u /\
  ghost_inv d cenv cx ee Gf tnf u /\
  ptr_vv_ok cx ann
    (PlaceR (StoragePlace tr (slot + n2w (1 + (len-1) * type_slot_size tv)) tv))
    (LocatedValue ann (mk_ptr op (if tr then LocTransient else LocStorage))) ee Gf tnf u /\
  ghost_kept cenv es sm G tn s Gf tnf
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\ evaluate_type (get_tenv cx) ann = SOME tv` by
    (drule nested_pop_storage_target_metadata >> simp[]) >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ stor_taint_ok cx tn s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def, ghost_inv_def] >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule nested_pop_array_header_load >> strip_tac >>
  `lookup_storage slot (if tr then contract_transient s else contract_storage s) =
     lookup_storage slot (get_storage cx es tr)` by
    (Cases_on `tr` >> gvs[sload_def, tload_def, contract_storage_def, contract_transient_def]) >>
  conj_tac >- suspend "semantic" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "returned" >>
  irule pop_root_endpoint_kept >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume pop_storage_positive_endpoint[semantic]:
  qabbrev_tac `su = (if tr then tstore slot (n2w (len-1)) s
    else sstore slot (n2w (len-1)) s) with vs_vars := u.vs_vars` >>
  `u = su with vs_inst_idx := k` by simp[Abbr `su`] >>
  `su.vs_vars = u.vs_vars` by simp[Abbr `su`] >>
  `eval_operand op su = eval_operand op u` by
    (qpat_assum `u = su with vs_inst_idx := k` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `op` >> simp_tac (srw_ss()) [NoAsms, eval_operand_def, lookup_var_def]) >>
  `!x. not_fresh_at sm x ==> lookup_var x su = lookup_var x s` by
    (qpat_assum `su.vs_vars = u.vs_vars` (fn th =>
       pure_rewrite_tac[lookup_var_def, th]) >>
     metis_tac[lookup_var_def]) >>
  qpat_x_assum `u = su with vs_inst_idx := k` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[vv_post_inst_idx] >>
  qpat_assum `ee = _` (fn th => pure_rewrite_tac[th]) >>
  irule pop_storage_positive_vv_post >>
  metis_tac[]
QED

Resume pop_storage_positive_endpoint[ghost]:
  qabbrev_tac `su = (if tr then tstore slot (n2w (len-1)) s
    else sstore slot (n2w (len-1)) s) with vs_vars := u.vs_vars` >>
  `u = su with vs_inst_idx := k` by simp[Abbr `su`] >>
  `su.vs_vars = u.vs_vars` by simp[Abbr `su`] >>
  `ee.scopes = es.scopes` by simp[set_storage_def] >>
  `!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x) /\
    lookup_var x su = lookup_var x s` by
    (qpat_assum `su.vs_vars = u.vs_vars` (fn th =>
       pure_rewrite_tac[lookup_var_def, th]) >> metis_tac[lookup_var_def]) >>
  qpat_x_assum `u = su with vs_inst_idx := k` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[hash_ghost_inv_inst_idx] >>
  irule pop_storage_endpoint_ghost >>
  qpat_assum `ghost_inv _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `declared_storage_region _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `storage_subregion _ _ _ _` (irule_at Any) >>
  qexistsl [`xs`, `sm`, `len`, `slot`] >>
  simp[Abbr `su`]
QED

Resume pop_storage_positive_endpoint[returned]:
  irule pop_storage_returned_place >>
  qpat_assum `stor_taint_ok _ _ _` (irule_at Any) >>
  qpat_assum `evaluate_type _ _ = _` (irule_at Any) >>
  qpat_assum `storage_read_live _ _ _ _ _` (irule_at Any) >>
  qexistsl [`n2w (len-1)`, `len`, `slot + n2w (1 + (len-1) * type_slot_size tv)`] >>
  simp[] >>
  qpat_x_assum `u = _ with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
  Cases_on `tr` >>
  gvs[contract_storage_def, contract_transient_def, sstore_def, tstore_def,
      vfmStateTheory.lookup_account_def]
QED

Finalise pop_storage_positive_endpoint

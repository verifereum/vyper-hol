(* Nested storage endpoints retain the declared root, not a fictitious
   declaration at the computed array header. *)
Theory bodyPtrPopStoragePurePost
Ancestors
  bodyPtrPopRootEndpoint bodyPtrPopRootGhost bodyPtrPopReturned
  exprSimPopNestedBase appendStorageGhostPtr bodyPtrDefs compileEnv
  exprLoweringProps venomState ptrDiscipline finite_map pred_set list
  vyperStorage accountsRelProps

Theorem pop_storage_header_taint_dead_subset:
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n root_slot + delta /\
  X SUBSET {(k,b) | storage_dead cx tr st (w2n k) b} ==>
  key_update X slot {} SUBSET
    {(k,b) | storage_dead cx tr
      (update_storage slot (n2w (w2n (lookup_storage slot st)-1)) st) (w2n k) b}
Proof
  strip_tac >> pure_rewrite_tac [SUBSET_DEF] >> Cases >>
  simp[key_update_def] >> strip_tac >>
  irule nested_pop_storage_dead_header >>
  conj_tac >- metis_tac[] >>
  gvs[SUBSET_DEF] >> first_x_assum drule >> simp[]
QED

Theorem pop_storage_header_stor_taint_ok:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n root_slot + delta /\
  len = w2n (lookup_storage slot
    (if tr then contract_transient s else contract_storage s)) /\
  tn'.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
  tn'.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
  tn'.t_imm = tn.t_imm ==>
  stor_taint_ok cx tn'
    (if tr then tstore slot (n2w (len-1)) s else sstore slot (n2w (len-1)) s)
Proof
  strip_tac >>
  `key_update (if tr then tn.t_trans else tn.t_stor) slot {} SUBSET
    {(k,b) | storage_dead cx tr
      (update_storage slot (n2w (len-1))
        (if tr then contract_transient s else contract_storage s)) (w2n k) b}` by
    (gvs[] >> irule pop_storage_header_taint_dead_subset >>
     reverse conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >> Cases_on `tr` >>
     gvs[stor_taint_ok_def, cx_dead_def, contract_storage_def,
         contract_transient_def, vfmStateTheory.lookup_account_def]) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, sstore_def, tstore_def,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem pop_storage_endpoint_ghost:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n hdr = w2n root_slot + delta /\
  len = w2n (lookup_storage hdr
    (if tr then contract_transient s else contract_storage s)) /\
  sf = (if tr then tstore hdr (n2w (len - 1)) s
        else sstore hdr (n2w (len - 1)) s) with vs_vars := sf.vs_vars /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  EVERY (\x. ~not_fresh_at sa x) xs /\
  (!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x) /\
       lookup_var x sf = lookup_var x s) /\
  ee.scopes = es.scopes /\ tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
  tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor hdr {}) /\
  tnf.t_trans = (if tr then key_update tn.t_trans hdr {} else tn.t_trans) ==>
  ghost_inv d cenv cx ee Gf tnf sf
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by fs[ghost_inv_def] >>
  `stor_taint_ok cx tnf
    (if tr then tstore hdr (n2w (len - 1)) s
     else sstore hdr (n2w (len - 1)) s)` by
    (irule pop_storage_header_stor_taint_ok >> simp[] >> metis_tac[]) >>
  `stor_taint_ok cx tnf sf /\ sf.vs_memory = s.vs_memory` by
    (qpat_x_assum `sf = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >> gvs[stor_taint_ok_def, sstore_def, tstore_def]) >>
  irule pop_ghost_inv_old_transport >> goal_assum (drule_at Any) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem pop_storage_returned_place:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  raw = (if tr then s.vs_transient s.vs_call_ctx.cc_address
         else (s.vs_accounts s.vs_call_ctx.cc_address).storage) /\
  storage_read_live cx tr raw hdr (ArrayTV tv (Dynamic cap)) /\
  len = w2n (lookup_storage hdr raw) /\ 0 < len /\ len <= cap /\
  elem = hdr + n2w (1 + (len - 1) * type_slot_size tv) /\
  (if tr then sf.vs_transient sf.vs_call_ctx.cc_address
   else (sf.vs_accounts sf.vs_call_ctx.cc_address).storage) =
    update_storage hdr u raw /\
  (if tr then tnf.t_trans else tnf.t_stor) =
    key_update (if tr then tn.t_trans else tn.t_stor) hdr {} /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  eval_operand op sf = SOME elem /\ op_taint tnf op = {} ==>
  ptr_vv_ok cx ann result
    (LocatedValue ann (mk_ptr op (if tr then LocTransient else LocStorage)))
    esf Gf tnf sf
Proof
  strip_tac >> irule pop_returned_place_of_region >> simp[] >>
  `(if tr then tn.t_trans else tn.t_stor) SUBSET
     {(k,b) | storage_dead cx tr raw (w2n k) b}` by
    (Cases_on `tr` >> gvs[stor_taint_ok_def, cx_dead_def]) >>
  irule pop_last_child_taint_header >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`cx`, `tr`] >> gvs[]
QED

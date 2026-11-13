Theory bodyPtrPopRootEndpoint
Ancestors
  bodyPtrPopRootGhost bodyPtrPopReturned appendStorageGhostPtr bodyPtrDefs
  compileEnv exprLoweringProps venomState ptrDiscipline finite_map pred_set list

Theorem pop_root_endpoint_ghost:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid name subs = SOME (tr,hdr,ArrayTV tv (Dynamic cap)) /\
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
    (irule pop_header_stor_taint_ok >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `stor_taint_ok cx tnf sf /\ sf.vs_memory = s.vs_memory` by
    (qpat_x_assum `sf = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >> gvs[stor_taint_ok_def, sstore_def, tstore_def]) >>
  irule pop_ghost_inv_old_transport >> goal_assum (drule_at Any) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem pop_root_endpoint_kept:
  EVERY (\x. ~not_fresh_at sa x) xs /\
  (!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
  tnf.t_mem = tn.t_mem ==>
  ghost_kept cenv es sa G tn s Gf tnf
Proof
  strip_tac >> irule ghost_kept_old_transport >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

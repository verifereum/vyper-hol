(* Storage-bank boundary facts for pointer-safe word append. *)
Theory appendStorageGhostPtr
Ancestors
  bodyPtrDefs appendStorageRel accountsRelProps ptrDiscipline
  compileEnv loweringStateRelDefs venomState vyperStorage words pred_set stmtFragPtr loweringPosts

Theorem storage_dead_key_taint_empty:
  X SUBSET {(k,b) | storage_dead cx tr st (w2n k) b} /\
  storage_read_live cx tr st slot tv /\ 0 < type_slot_size tv ==>
  key_taint X slot = {}
Proof
  rw[key_taint_def, EXTENSION] >>
  gvs[SUBSET_DEF] >>
  drule_all storage_read_live_head >> strip_tac >>
  Cases_on `x < 32` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `(slot,x)` mp_tac) >> simp[]
QED

Theorem declared_header_key_taint_empty:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
  0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >> irule storage_dead_key_taint_empty >>
  qexistsl_tac [`cx`,
    `if tr then contract_transient s else contract_storage s`, `tr`, `tv`] >>
  simp[] >> conj_tac
  >- (Cases_on `tr` >>
      gvs[stor_taint_ok_def, cx_dead_def, contract_storage_def,
          contract_transient_def, vfmStateTheory.lookup_account_def]) >>
  metis_tac[declared_storage_region_read_live]
QED

Theorem append_clean_keys_dead_subset:
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  X SUBSET {(k,b) | storage_dead cx tr st (w2n k) b} ==>
  key_update (key_update X (slot+n2w (1+len)) {}) slot {} SUBSET
    {(k,b) | storage_dead cx tr
      (update_storage slot (n2w (len+1))
        (update_storage (slot+n2w (1+len)) w st)) (w2n k) b}
Proof
  strip_tac >> pure_rewrite_tac [SUBSET_DEF] >>
  Cases >> simp[key_update_def] >> strip_tac >>
  drule append_storage_dead_mono >>
  disch_then (qspecl_then [`w`, `st`, `len`, `w2n q`, `r`] mp_tac) >>
  simp[] >>
  gvs[SUBSET_DEF] >>
  qpat_x_assum `!x. x IN X ==> _` (qspec_then `(q,r)` mp_tac) >>
  simp[]
QED

Theorem append_clean_stores_taint_ok:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot
    (if tr then contract_transient s else contract_storage s)) /\ len < cap ==>
  stor_taint_ok cx
    (if tr then tn with t_trans :=
       key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {}
     else tn with t_stor :=
       key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {})
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  strip_tac >>
  `key_update (key_update (if tr then tn.t_trans else tn.t_stor)
      (slot+n2w (1+len)) {}) slot {} SUBSET
    {(k,b) | storage_dead cx tr
      (update_storage slot (n2w (len+1))
        (update_storage (slot+n2w (1+len)) w
          (if tr then contract_transient s else contract_storage s))) (w2n k) b}` by
    (irule append_clean_keys_dead_subset >>
     goal_assum (drule_at Any) >> simp[] >>
     Cases_on `tr` >>
     gvs[stor_taint_ok_def, cx_dead_def, contract_storage_def,
         contract_transient_def, vfmStateTheory.lookup_account_def] >>
     metis_tac[]) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, sstore_def, tstore_def,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem ptr_covers_old_transport:
  ptr_covers G tn p s sz /\ not_fresh_at sa p /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x) /\
       lookup_var x s' = lookup_var x s) ==>
  ptr_covers G' tn' p s' sz
Proof
  rw[ptr_covers_def] >> metis_tac[]
QED

Theorem ghost_inv_old_transport:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x) /\
       lookup_var x s' = lookup_var x s) /\
  es'.scopes = es.scopes /\ s'.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem /\ stor_taint_ok cx tn' s' ==>
  ghost_inv d cenv cx es' G' tn' s'
Proof
  strip_tac >> fs[ghost_inv_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      qpat_x_assum `!name entry p sz. _` drule >>
      disch_then drule >> strip_tac >>
      conj_tac
      >- (irule ptr_covers_old_transport >>
          goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def] >>
      irule ptr_covers_old_transport >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> metis_tac[ret_pc_ok_def]
QED

Theorem ghost_kept_old_transport:
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  rw[ghost_kept_def] >> fs[SUBSET_DEF]
QED

Theorem ghost_kept_suffix_compose:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. not_fresh_at sb x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  rw[ghost_kept_def] >> fs[SUBSET_DEF] >>
  metis_tac[not_fresh_at_mono]
QED

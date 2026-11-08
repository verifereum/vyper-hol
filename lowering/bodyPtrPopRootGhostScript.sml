Theory bodyPtrPopRootGhost
Ancestors
  bodyPtrDefs exprSimPopStorage appendStorageGhostPtr ptrDiscipline
  venomState vyperStorage words pred_set compileEnv

Theorem pop_header_taint_dead_subset:
  declared_storage_region cx mid name subs =
    SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  X SUBSET {(k,b) | storage_dead cx tr st (w2n k) b} ==>
  key_update X slot {} SUBSET
    {(k,b) | storage_dead cx tr
      (update_storage slot (n2w (w2n (lookup_storage slot st)-1)) st) (w2n k) b}
Proof
  strip_tac >> pure_rewrite_tac [SUBSET_DEF] >> Cases >>
  simp[key_update_def] >> strip_tac >>
  irule storage_dead_pop_header >> conj_tac
  >- (goal_assum (drule_at Any)) >>
  gvs[SUBSET_DEF] >> first_x_assum drule >> simp[]
QED

Theorem pop_header_stor_taint_ok:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid name subs =
    SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
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
    (gvs[] >> irule pop_header_taint_dead_subset >>
     conj_tac >- (goal_assum (drule_at Any)) >> Cases_on `tr` >>
     gvs[stor_taint_ok_def, cx_dead_def, contract_storage_def,
         contract_transient_def, vfmStateTheory.lookup_account_def]) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, sstore_def, tstore_def,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

(* The expression judgment provides freshness directly for both return
   operands; no stronger return-PC runtime condition is necessary. *)
Theorem pop_ghost_inv_old_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x) /\
       lookup_var x s' = lookup_var x s) /\
  es'.scopes = es.scopes /\ s'.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem /\ stor_taint_ok cx tn' s' ==>
  ghost_inv d cenv cx es' G' tn' s'
Proof
  strip_tac >> fs[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      qpat_x_assum `!name entry p sz. _` drule >>
      disch_then drule >> strip_tac >> conj_tac
      >- (irule ptr_covers_old_transport >>
          goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `d` >> fs[return_buf_ptr_def] >> PairCases_on `x` >>
  gvs[return_buf_ptr_def] >> metis_tac[ptr_covers_old_transport]
QED

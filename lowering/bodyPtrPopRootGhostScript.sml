Theory bodyPtrPopRootGhost
Ancestors
  bodyPtrDefs exprSimPopStorage appendStorageGhostPtr ptrDiscipline
  venomState vyperStorage words pred_set

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

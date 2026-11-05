Theory bodyPtrPopSavedRegion
Ancestors
  bodyPtrPopBoundary bodyPtrPopTaintProbe exprSimPopStorage
  accountsRelProps vyperStorage vyperValue words pred_set vfmState

(* Raw equality, unlike global liveness, survives shortening an ancestor.
   The written values need not agree when the write misses the saved read. *)
Theorem pop_saved_lookup_header:
  !st rt (hdr:bytes32) u v k.
    k <> hdr /\ lookup_storage k rt = lookup_storage k st ==>
    lookup_storage k (update_storage hdr v rt) =
    lookup_storage k (update_storage hdr u st)
Proof
  rpt strip_tac >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  gvs[lookup_storage_def]
QED

Theorem pop_saved_range_header:
  !st rt (hdr:bytes32) u v w tv.
    storage_range_agree st rt w tv /\ w2n hdr < w2n w ==>
    storage_range_agree (update_storage hdr u st)
      (update_storage hdr v rt) w tv
Proof
  rpt strip_tac >> irule storage_range_agree_frame >>
  qexistsl [`st`, `rt`] >> simp[] >> rpt strip_tac >>
  `i < dimword (:256)` by
    gvs[storage_range_agree_def] >>
  `(n2w i:bytes32) <> hdr` by
    (disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     asm_simp_tac pure_ss [w2n_n2w, arithmeticTheory.LESS_MOD] >> simp[]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* A local, type-relative taint bound is retained even when the ancestor's
   length update makes the saved child globally dead. *)
Theorem pop_saved_child_taint_header:
  !st (hdr:bytes32) u base tv tn inst s s' addr v key.
    w2n hdr < base /\ base + type_slot_size tv <= dimword (:256) /\
    inst.inst_operands = [addr; v] /\ eval_operand addr s = SOME key /\
    op_taint tn v = {} /\
    (!k b. (k,b) IN tn.t_stor /\ base <= w2n k /\
           w2n k < base + type_slot_size tv ==> dead_bytes st base tv (w2n k) b) ==>
    !k b. (k,b) IN (step_taint inst s s' tn).t_stor /\ base <= w2n k /\
           w2n k < base + type_slot_size tv ==>
      dead_bytes (update_storage hdr u st) base tv (w2n k) b
Proof
  rpt gen_tac >> strip_tac >>
  drule_all pop_clean_header_step_taint >>
  simp[SUBSET_DEF] >> strip_tac >> rpt strip_tac >>
  drule_all pop_child_dead_bytes_header >>
  disch_then (qspecl_then [`st`, `u`, `w2n k`, `b`] mp_tac) >>
  metis_tac[]
QED

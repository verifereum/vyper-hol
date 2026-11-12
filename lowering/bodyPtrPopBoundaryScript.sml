Theory bodyPtrPopBoundary
Ancestors
  accountsRelProps vyperStorage vyperValue words finite_map vfmState

(* The child's dead-byte specification survives a write strictly below its
   region.  Unlike the outer array's liveness, this does not depend on the
   new length. *)
Theorem pop_child_dead_bytes_header:
  !st (hdr:bytes32) u base tv j b.
    w2n hdr < base /\ base + type_slot_size tv <= dimword (:256) ==>
    (dead_bytes (update_storage hdr u st) base tv j b <=>
     dead_bytes st base tv j b)
Proof
  rpt strip_tac >> irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  `i < dimword (:256) /\ i <> w2n hdr` by decide_tac >>
  `(n2w i:bytes32) <> hdr` by
    (disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     asm_simp_tac pure_ss [w2n_n2w, arithmeticTheory.LESS_MOD] >> simp[]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

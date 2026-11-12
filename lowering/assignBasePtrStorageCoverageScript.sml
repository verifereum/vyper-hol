(* Reuse the address-specific coverage boundary; sites may cross dimword. *)
Theory assignBasePtrStorageCoverage
Ancestors assignBasePtrOffset arithmetic

Theorem assign_base_ptr_covers_storage_word:
  !G tn p s total w b cap i k G' tn' q s'.
    ptr_covers G tn p s total /\ lookup_var p s = SOME w /\
    FLOOKUP G p = SOME (b,cap) /\
    i < k /\ 32*k <= total /\
    w2n w + 32*(k-1) < dimword(:256) /\
    lookup_var q s' = SOME (w + n2w (32*i)) /\
    FLOOKUP G' q = SOME (b,cap) /\
    op_taint tn' (Var q) = {} ==>
    ptr_covers G' tn' q s' 32
Proof
  rpt strip_tac >>
  irule assign_base_ptr_covers_offset_address >>
  simp[] >>
  goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  qexistsl_tac [`32*i`, `w`] >> simp[] >> decide_tac
QED

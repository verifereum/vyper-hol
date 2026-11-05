(* Footprint-limited pointer coverage and offset arithmetic. *)
Theory ptrCoverage
Ancestors
  bodyPtrDefs words finite_map

Theorem ptr_covers_offset:
  !G tn p s total w b cap off n G' tn' q s'.
    ptr_covers G tn p s total /\ lookup_var p s = SOME w /\
    FLOOKUP G p = SOME (b,cap) /\ b + cap <= dimword(:256) /\
    off < total /\ off + n <= total /\
    lookup_var q s' = SOME (w + n2w off) /\
    FLOOKUP G' q = SOME (b,cap) /\
    op_taint tn' (Var q) = {} ==>
    ptr_covers G' tn' q s' n
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  `w2n w + off < dimword(:256)` by decide_tac >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptr_covers_def, w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

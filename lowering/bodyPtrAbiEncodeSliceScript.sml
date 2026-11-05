(* Resource slices independent of semantic layout.  Unlike ptr_covers_offset,
   explicit no-wrap permits an empty slice at the root's right endpoint. *)
Theory bodyPtrAbiEncodeSlice
Ancestors
  bodyPtrDefs ptrCoverage venomState words finite_map arithmetic pred_set

Theorem ptr_covers_slice_no_wrap:
  !G tn p s total w off n q s' G' tn'.
  ptr_covers G tn p s total /\ lookup_var p s = SOME w /\
  off+n <= total /\ w2n w+off < dimword(:256) /\
  lookup_var q s' = SOME (w+n2w off) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' n
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptr_covers_def, w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac
QED

Theorem clean_window_slice:
  !(off:num) n total B tainted.
  off+n <= total /\
  (!i. B <= i /\ i < B+total ==> i NOTIN tainted) ==>
  !i. B+off <= i /\ i < B+off+n ==> i NOTIN tainted
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum irule >> decide_tac
QED

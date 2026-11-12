Theory extRetNormalizeWindowPtr
Ancestors
  extRetNormalizeRangePtr extRetNormalizeInputsPtr typedCopyLayoutPtr

Theorem positive_footprint_window_bound:
  !(b:num) a foot sz off n.
    b <= a /\ a+foot <= b+sz /\ b+sz < dimword (:256) /\
    off+n <= foot /\ 0<n ==>
    b <= a+off /\ a+off+n <= b+sz /\ a+off+n < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

Theorem allocated_footprint_window_bound:
  !ctx fn ce cx es s aid b sz a foot off n.
    stmt_state_rel ctx fn ce cx es s /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    b <= a /\ a+foot <= b+sz /\ off+n <= foot /\ 0<n ==>
    b <= a+off /\ a+off+n <= b+sz /\ a+off+n < dimword (:256)
Proof
  rpt strip_tac >>
  `b+sz < dimword (:256)` by
    (drule_all stmt_state_rel_alloca_end_bound >> simp[]) >>
  decide_tac
QED

(* Existing dynarray_length_footprint_contained already proves the header
   size bound, without a typing premise and including vs=[]. Reuse it. *)
Theorem dynarray_header_window_bound:
  !tv cap vs b a sz.
    b <= a /\
    a + val_footprint (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      <= b+sz /\ b+sz < dimword (:256) ==>
    b <= a /\ a+32 <= b+sz /\ a+32 < dimword (:256)
Proof
  rpt strip_tac >>
  qspecl_then [`tv`, `cap`, `vs`] assume_tac
    dynarray_length_footprint_contained >> decide_tac
QED

(* The allocated alternative has its strict endpoint discharged above.
   A local-region caller must still supply b+sz < dimword (:256) to the
   arithmetic boundary. No claim about G identifying concrete allocations,
   no zero-byte address claim, and no unequal-type representation conversion
   is made by these window lemmas. *)

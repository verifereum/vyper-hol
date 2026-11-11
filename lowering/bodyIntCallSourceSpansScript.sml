(* Full physical-capacity projections; no producer provenance is asserted here. *)
Theory bodyIntCallSourceSpans
Ancestors
  placeMemoryCopyFrames arithmetic

Theorem source_span_above_frontier:
  !d dn lo a s n k M:num.
    d + dn <= lo /\ lo <= a /\ a <= s /\
    s + n <= a + k /\ a + k < M ==>
    s + n < M /\ (s + n <= d \/ d + dn <= s)
Proof
  rpt strip_tac >> decide_tac
QED

Theorem source_span_in_separated_slot:
  !a s n k M d dn:num.
    a <= s /\ s + n <= a + k /\ a + k < M /\
    (a + k <= d \/ d + dn <= a) ==>
    s + n < M /\ (s + n <= d \/ d + dn <= s)
Proof
  rpt strip_tac >> decide_tac
QED

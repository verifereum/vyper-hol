(* A well-formed selected value occupies no more than its containing layout. *)
Theory bodyIntCallPostProvenanceFootprint
Ancestors
  loweringPosts exprSimProps

Theorem sub_layout_footprint_bound:
  sub_layout bt bv k tv v /\ val_wf tv v ==>
  k + val_footprint tv v <= type_memory_size bt
Proof
  strip_tac >>
  drule val_footprint_le >>
  gvs[sub_layout_def]
QED

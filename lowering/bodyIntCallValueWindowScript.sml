(* Typed values survive equality of any containing byte window.  The
   semantic footprint includes dynamic-array headers and nested values. *)
Theory bodyIntCallValueWindow
Ancestors
  exprSimProps valueEncodingProofs

Theorem val_in_memory_window_agree:
  mem_bytes_at b sz mem' = mem_bytes_at b sz mem /\
  val_in_memory tv v p mem /\ val_wf tv v /\
  b <= p /\ p + val_footprint tv v <= b + sz ==>
  val_in_memory tv v p mem'
Proof
  strip_tac >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  irule val_in_memory_footprint_agree >> metis_tac[]
QED

(* Semantic values inside old, local-disjoint allocations survive an
   expression's actual vv_post endpoint. *)
Theory bodyIntCallArgOwnedFrame
Ancestors
  exprSimAggregateChildren exprSimProps valueEncodingProofs

Theorem vv_post_old_buffer_value:
  vv_post ctx func cenv cx e es sm sn s0 ee raw vv s /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
  (!n b lsz. local_region cenv es.scopes s0 n b lsz ==>
    off + sz <= b \/ b + lsz <= off) /\
  val_in_memory tv v p s0.vs_memory /\ val_wf tv v /\
  off <= p /\ p + val_footprint tv v <= off + sz ==>
  val_in_memory tv v p s.vs_memory
Proof
  strip_tac >>
  drule_all vv_post_old_buffer >>
  disch_then (strip_assume_tac o MATCH_MP mem_bytes_at_agree_window) >>
  irule val_in_memory_footprint_agree >> metis_tac[]
QED

(* Physical copy observations preserve the caller's writeback frame. *)
Theory bodyIntCallCopyFrame
Ancestors
  bodyIntCallStorePost exprSimStorageCopy

Theorem copy_prefix_owned_wb_frame:
  wb_frame ce es0 sa s0 u /\ alloca_inv u /\
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  sa.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x z = lookup_var x u) /\
  copy_prefix loc a b n u k z /\ 32*n <= sz /\
  (!name lb lsz. local_region ce es0.scopes s0 name lb lsz ==>
    lb+lsz <= b \/ b+sz <= lb) ==>
  wb_frame ce es0 sa s0 z
Proof
  strip_tac >>
  `z.vs_allocas = u.vs_allocas` by
    metis_tac[copy_prefix_def, copy_static_fields] >>
  `!off len. off+len <= b \/ b+sz <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory` by
    (rpt strip_tac >> irule copy_prefix_bytes >>
     qexistsl_tac [`a`, `b`, `k`, `loc`, `n`] >> simp[] >> decide_tac) >>
  irule wb_frame_owned_memory_tail >> metis_tac[]
QED

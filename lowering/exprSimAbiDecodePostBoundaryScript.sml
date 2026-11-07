(* Consumer-facing elimination of the decoder's control-closed post. *)
Theory exprSimAbiDecodePostBoundary
Ancestors
  exprSimAbiDecodePost

Theorem abi_decode_post_closure_mono:
  (!u. post u ==> post' u) /\ abi_decode_post_closure post s ==>
  abi_decode_post_closure post' s
Proof
  rw[abi_decode_post_closure_def] >>
  qexistsl [`u`, `rd`, `p`] >> simp[]
QED

Theorem abi_decode_post_closure_implies_vv_post:
  (!u. post u ==> vv_post ctx func ce cx e es sa sb s0 es' tv vv u) /\
  abi_decode_post_closure post s ==>
  vv_post ctx func ce cx e es sa sb s0 es' tv vv s
Proof
  strip_tac >> irule abi_decode_post_closure_vv_post >>
  irule abi_decode_post_closure_mono >> goal_assum (drule_at Any) >> simp[]
QED

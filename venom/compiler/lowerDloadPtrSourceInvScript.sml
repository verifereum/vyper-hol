Theory lowerDloadPtrSourceInv
Ancestors
  frameRawReachable unitMemInv o1PassContract lowerDloadDefs unitTransformDefs

Theorem mem_inv_frame_reachable:
  o1_ctx_shape ctx /\ mem_inv M ctx vs /\
  frame_reachable vs ctx stk PG G tn fn inst s ==> M ctx fn inst s
Proof
  strip_tac >> drule_all frame_reachable_raw >>
  fs[mem_inv_raw_reachable]
QED

Theorem o1_src_frame_raw_mem_ok:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s ==> raw_mem_ok C fn inst s
Proof
  strip_tac >> irule mem_inv_frame_reachable >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

Theorem o1_src_frame_dload_offset_ok:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s ==> dload_offset_ok C fn inst s
Proof
  strip_tac >> irule mem_inv_frame_reachable >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

Theorem o1_src_frame_dload_headroom_ok:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s ==> dload_headroom_ok C fn inst s
Proof
  strip_tac >> irule mem_inv_frame_reachable >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

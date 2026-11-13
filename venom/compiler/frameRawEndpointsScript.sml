Theory frameRawEndpoints
Ancestors frameRawProjection frameActivationSeparation frameActivationCache
  unitMemInv venomMemProps venomMemDefs venomState finite_map list arithmetic words

Theorem frame_reachable_mem_inv:
  EVERY wf_function ctx.ctx_functions /\ mem_inv M ctx vs0 /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==> M ctx fn inst s
Proof
  simp[mem_inv_raw_reachable] >> metis_tac[frame_reachable_raw]
QED

Theorem frame_reachable_saved_mem_inv:
  EVERY wf_function ctx.ctx_functions /\ mem_inv M ctx vs0 /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  EVERY (\f. M ctx f.cf_fn f.cf_inst f.cf_state) stk
Proof
  strip_tac >> drule_all frame_reachable_saved_raw >>
  fs[mem_inv_raw_reachable, EVERY_MEM] >> metis_tac[]
QED

Theorem joint_reachable_raw_frontier:
  EVERY wf_function ctx.ctx_functions /\ mem_inv raw_mem_ok ctx vs0 /\
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn fn inst s oms om hs h) ==>
  s.vs_alloca_next < dimword (:256)
Proof
  simp[mem_inv_raw_reachable] >> rpt strip_tac >>
  drule_all joint_config_raw >>
  metis_tac[raw_mem_ok_def]
QED

Theorem joint_activation_cache_strict:
  EVERY wf_function ctx.ctx_functions /\ mem_inv raw_mem_ok ctx vs0 /\
  vs0.vs_allocas = FEMPTY /\
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    depth owner aid (b,sz) ==>
  b + sz < dimword (:256)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule_all joint_reachable_raw_frontier >> simp[]) >>
  drule_all joint_reachable_cache_separated >> strip_tac >>
  gvs[activation_cache_def]
  >- (drule frame_cache_separated_local >>
      simp[alloca_inv_def, alloca_next_valid_def] >>
      metis_tac[LESS_EQ_LESS_TRANS]) >>
  `LENGTH stk - SUC depth < LENGTH stk` by decide_tac >>
  drule_all frame_cache_saved_bound >> decide_tac
QED

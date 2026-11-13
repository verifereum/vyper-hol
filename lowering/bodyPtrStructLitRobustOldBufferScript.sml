Theory bodyPtrStructLitRobustOldBuffer
Ancestors bodyPtrStructLitMonotoneRepresentation exprSimAggregateChildren
  bodyPtrDefs loweringPosts valueEncodingProofs valueEncoding
  venomState compileEnv finite_map

Theorem structlit_old_robust_value_preserved:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s1 /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+n <= lo \/ lo+sz <= b) /\
  val_wf vt v /\ b <= p /\ p + val_footprint vt v <= b+n /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory vt v p m) ==>
  !m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
    val_in_memory vt v p m
Proof
  strip_tac >>
  `mem_bytes_at p (val_footprint vt v) s1.vs_memory =
   mem_bytes_at p (val_footprint vt v) s0.vs_memory` by
    (drule_all vv_post_old_buffer >> strip_tac >>
     drule (cj 1 mem_bytes_at_agree_window) >>
     disch_then (qspecl_then [`p`, `val_footprint vt v`] mp_tac) >> simp[]) >>
  `!i. i < val_footprint vt v ==>
    (p+i IN tn1.t_mem ==> p+i IN tn0.t_mem)` by
    (qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_kept_def] >> rpt strip_tac >>
     `b <= p+i /\ p+i < b+n` by decide_tac >>
     fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport_mono >>
  simp[] >>
  qexistsl [`s0.vs_memory`, `s1.vs_memory`, `val_footprint vt v`,
    `p`, `tn0.t_mem`, `tn1.t_mem`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* An initialized old allocation is stable under both semantic memory framing
   and the no-new-taint part of ghost_kept. *)
Theory bodyPtrMakeArrayPrefixFrame
Ancestors
  bodyPtrMakeArrayMemoryFrame bodyPtrMakeArrayFrame bodyPtrMakeArrayAddCoverage
  exprSimAggregateChildren bodyPtrDefs
  loweringPosts valueEncoding venomState

Theorem child_old_allocation_robust:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region cenv es.scopes s0 n b k ==>
    off + sz <= b \/ b + k <= off) /\
  val_wf ty v /\ val_footprint ty v <= sz /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
        val_in_memory ty v off m) ==>
  !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ty v off m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all vv_post_old_buffer >> strip_tac >>
  rpt strip_tac >> irule robust_val_in_memory_shrinking_frame >>
  simp[] >>
  qexistsl_tac [`tn0.t_mem`, `tn.t_mem`, `s0.vs_memory`, `s.vs_memory`, `sz`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem child_old_pointer_coverage:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa root /\ ptr_covers G0 tn0 root s0 capacity ==>
  ptr_covers G tn root s capacity
Proof
  strip_tac >>
  qpat_x_assum `ptr_covers _ _ _ _ _` mp_tac >>
  simp[ptr_covers_def] >> strip_tac >>
  drule_all child_old_variable_preserved >> strip_tac >>
  simp[ptr_covers_def] >> metis_tac[]
QED

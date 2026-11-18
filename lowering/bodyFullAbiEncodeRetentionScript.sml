(* Anonymous owned operands survive a continuing child full outcome.
   Representation framing concerns the value footprint, not capacity padding. *)
Theory bodyFullAbiEncodeRetention
Ancestors
  bodySimFull assignTuplePtrCopyLen logValueFramePtr
  representationCleanPtr abiDecodeStaticProps allocaHistory
  loweringPosts bodyPtrDefs arithmetic words

Theorem abi_encode_owned_operand_retained:
  expr_post H ctx func ce cx e es sa sb s ee v op t /\
  ghost_kept_at lo ce es sa G tn s G' tn' /\
  ghost_inv_at D lo d ce cx ee G' tn' t /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  not_fresh_at sa x /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s capacity /\ val_wf tv value /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv value (w2n w) mem) /\
  FLOOKUP s.vs_allocas aid = SOME (rowbase,sz) /\ aid < sa.cs_next_id /\
  rowbase <= w2n w /\ w2n w + val_footprint tv value <= rowbase + sz /\
  (!n b k. local_region ce es.scopes s n b k ==>
    rowbase + sz <= b \/ b + k <= rowbase) ==>
  lookup_var x t = SOME w /\
  ptr_covers G' tn' x t capacity /\
  (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv value (w2n w) mem) /\
  FLOOKUP t.vs_allocas aid = SOME (rowbase,sz) /\
  mem_bytes_at rowbase sz t.vs_memory = mem_bytes_at rowbase sz s.vs_memory /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `lookup_var x t = SOME w /\
   FLOOKUP t.vs_allocas aid = SOME (rowbase,sz) /\
   mem_bytes_at rowbase sz t.vs_memory = mem_bytes_at rowbase sz s.vs_memory` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `FLOOKUP G' x = FLOOKUP G x /\
   op_taint tn' (Var x) = op_taint tn (Var x)` by
    (fs[ghost_kept_at_def] >> metis_tac[]) >>
  `ptr_covers G' tn' x t capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv value) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv value) s.vs_memory` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     irule mem_bytes_at_eq_byte >> qexistsl_tac [`rowbase`, `sz`] >> simp[] >> decide_tac) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv value /\
       i IN tn'.t_mem ==> i IN tn.t_mem` by
    (fs[ghost_kept_at_def] >> rpt strip_tac >>
     qpat_x_assum `!a off k i. FLOOKUP s.vs_allocas a = SOME (off,k) /\ _ ==> _`
       (qspecl_then [`aid`, `rowbase`, `sz`, `i`] mp_tac) >>
     impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[]) >> simp[]) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
     val_in_memory tv value (w2n w) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_footprint_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >> simp[]) >>
  fs[ghost_inv_at_def]
QED

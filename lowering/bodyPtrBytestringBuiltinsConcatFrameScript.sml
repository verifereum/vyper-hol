(* Old nonlocal allocation windows survive arbitrary child evaluation. *)
Theory bodyPtrBytestringBuiltinsConcatFrame
Ancestors
  bodyPtrDefs loweringPosts bodyPtrIfExpAllocProbe
  finite_map pred_set

Theorem concat_operand_old_allocation_frame:
  expr_post ctx fn ce cx e es sa sb s0 ee v op s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name off len. local_region ce es.scopes s0 name off len ==>
     b+sz <= off \/ off+len <= b) ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory /\
  (!i. b <= i /\ i < b+sz /\ i NOTIN tn0.t_mem ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> conj_tac
  >- (fs[expr_post_def] >>
      qpat_x_assum `!aid off sz. _` irule >>
      metis_tac[arithmeticTheory.ADD_SYM]) >>
  fs[ghost_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!aid off sz i. _` (qspecl_then [`aid`,`b`,`sz`,`i`] mp_tac) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_SYM]
QED

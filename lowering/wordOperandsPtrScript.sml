(* Shared frames for left-to-right operand evaluation.  The separation
   premise is essential: evaluating a later operand may mutate a local. *)
Theory wordOperandsPtr
Ancestors
  bodyPtrDefs exprSimWordArgs loweringPosts finite_map pred_set

Theorem operand_saved_allocation_frame:
  wb_frame cenv es sa s0 s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
  (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
             off + sz <= b \/ b + sz' <= off) ==>
  FLOOKUP s.vs_allocas aid = SOME (off, sz) /\
  mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory /\
  (!i. off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)
Proof
  simp[wb_frame_def, ghost_kept_def] >> metis_tac[]
QED

Theorem operand_saved_pointer_frame:
  wb_frame cenv es sa s0 s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 sz ==>
  ptr_covers G tn p s sz
Proof
  simp[wb_frame_def, ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

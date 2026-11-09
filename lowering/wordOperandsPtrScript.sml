(* Shared frames for left-to-right operand evaluation.  The separation
   premise is essential: evaluating a later operand may mutate a local. *)
Theory wordOperandsPtr
Ancestors
  bodyPtrDefs exprSimWordArgs exprSimProps freshWrites loweringPosts finite_map pred_set

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

Theorem ghost_kept_trans:
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 /\
  wb_frame cenv es sa s0 s1 /\
  local_ptrs_rel func cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv es1.scopes s1 n b sz` by
    (gvs[wb_frame_def] >> rpt gen_tac >> eq_tac >> strip_tac
     >- (irule local_region_frame_fwd >> metis_tac[]) >>
     irule local_region_frame >> metis_tac[]) >>
  gvs[ghost_kept_def, wb_frame_def] >>
  rpt conj_tac
  >- metis_tac[not_fresh_at_mono]
  >- (rpt strip_tac >>
      `aid < sb.cs_next_id` by decide_tac >> metis_tac[]) >>
  metis_tac[]
QED

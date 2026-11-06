Theory bodyPtrBytestringBuiltinsConcatFrame
Ancestors
  bodyPtrDefs wordArgsPtr exprSimDefs exprSimProps concatMemory
  finite_map pred_set arithmetic

(* Older scratch allocations cannot acquire taint while an operand runs.
   Contents are transported separately by expr_post, not by this fact. *)
Theorem ghost_kept_old_allocation_clean_range:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  b <= p /\ p + n <= b + sz /\
  (!i. p <= i /\ i < p + n ==> i NOTIN tn0.t_mem) ==>
  (!i. p <= i /\ i < p + n ==> i NOTIN tn.t_mem)
Proof
  rw[ghost_kept_def] >>
  `b <= i /\ i < b + sz` by decide_tac >> metis_tac[]
QED

(* One general scratch-allocation frame serves both the output prefix and
   the mutable offset cell. No claim is made about unrelated memory. *)
Theorem expr_operand_old_allocation_frame:
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  b <= p /\ p + n <= b + sz /\
  (!i. p <= i /\ i < p + n ==> i NOTIN tn0.t_mem) ==>
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory /\
  (!i. p <= i /\ i < p + n ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!i. p <= i /\ i < p + n ==> i NOTIN tn.t_mem` by
    metis_tac[ghost_kept_old_allocation_clean_range] >>
  fs[loweringPostsTheory.expr_post_def] >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory` by
    metis_tac[] >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum (qspecl_then [`p`,`n`] mp_tac) >> simp[]
QED

Theorem expr_operand_old_pointer_frame:
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa x /\
  lookup_var x s0 = SOME w ==>
  lookup_var x t = SOME w /\ FLOOKUP G x = FLOOKUP G0 x /\
  op_taint tn (Var x) = op_taint tn0 (Var x) /\
  (ptr_covers G0 tn0 x s0 capacity ==> ptr_covers G tn x t capacity)
Proof
  simp[loweringPostsTheory.expr_post_def, ghost_kept_def,
       ptr_covers_def] >> metis_tac[]
QED

Theorem expr_operand_old_offset_frame:
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  b <= p /\ p + 32 <= b + sz /\
  (!i. p <= i /\ i < p + 32 ==> i NOTIN tn0.t_mem) ==>
  mload p t = mload p s0 /\
  (!i. p <= i /\ i < p + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all expr_operand_old_allocation_frame >> strip_tac >>
  simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  fs[valueEncodingTheory.mem_word_at_def, valueEncodingTheory.mem_bytes_at_def]
QED

Theorem expr_operand_scratch_disjoint:
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  (!name lb lsz. local_region cenv ee.scopes t name lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  fs[loweringPostsTheory.expr_post_def] >> rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s0 name lb lsz` by
    (irule local_region_frame >> metis_tac[]) >> metis_tac[]
QED

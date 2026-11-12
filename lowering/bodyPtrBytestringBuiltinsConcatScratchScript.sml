(* Scratch windows survive arbitrary successful operand evaluation. *)
Theory bodyPtrBytestringBuiltinsConcatScratch
Ancestors
  bodyPtrBytestringBuiltinsConcatFrame exprSimConcatArgs bodyPtrDefs
  loweringPosts compileEnv venomState words arithmetic finite_map list

Theorem concat_args_pre_ptr:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v op t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  not_fresh_at sa dv /\ not_fresh_at sa ov /\
  lookup_var dv s0 = SOME (n2w (B+32)) /\ lookup_var ov s0 = SOME ow /\
  FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
  binst.inst_id < sa.cs_next_id /\
  FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  oinst.inst_id < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  32+k <= bsz /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ptr_covers G0 tn0 dv s0 (bsz-32) /\ ptr_covers G0 tn0 ov s0 32 /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn0.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn0.t_mem) ==>
  lookup_var dv t = SOME (n2w (B+32)) /\ lookup_var ov t = SOME ow /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es1.scopes t name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  mload (w2n ow) t = mload (w2n ow) s0 /\
  mem_bytes_at (B+32) k t.vs_memory = mem_bytes_at (B+32) k s0.vs_memory /\
  ptr_covers G tn dv t (bsz-32) /\ ptr_covers G tn ov t 32 /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all concat_args_pre >> strip_tac >>
  `ptr_covers G tn dv t (bsz-32) /\ ptr_covers G tn ov t 32` by
    (fs[ghost_kept_def, ptr_covers_def] >> gvs[]) >>
  `!i. B <= i /\ i < B+bsz /\ i NOTIN tn0.t_mem ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >>
     qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [ghost_kept_def] >> strip_tac >>
     qpat_x_assum `!aid off sz i. _` (qspecl_then [`binst.inst_id`, `B`, `bsz`, `i`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!i. w2n ow <= i /\ i < w2n ow+64 /\ i NOTIN tn0.t_mem ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >>
     qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [ghost_kept_def] >> strip_tac >>
     qpat_x_assum `!aid off sz i. _` (qspecl_then [`oinst.inst_id`, `w2n ow`, `64`, `i`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

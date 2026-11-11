(* Whole-local memory preservation permits removal of taint, without requiring
   an exact exterior taint equality as in the scratch-store boundary. *)
Theory bodyPtrSubscriptSeamMapFrame
Ancestors
  bodyPtrDefs bodyPtrHashBuiltinsGhostFrame logValueFramePtr
  exprSimProps exprLoweringProps compileEnv loweringStateRelDefs valueEncodingProps
  venomState finite_map pred_set

Theorem hash_local_robust_region_frame:
  !ctx fn cenv cx es s tn t tn' name entry p sz w.
    stmt_state_rel ctx fn cenv cx es s /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ tn'.t_mem SUBSET tn.t_mem /\
    (!n b k. local_region cenv es.scopes s n b k ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m) ==>
    !m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    metis_tac[local_ptrs_rel_def] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `mem_bytes_at (w2n w) sz t.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory` by
    metis_tac[] >>
  `mem_bytes_at (w2n w) (val_footprint entry.type entry.value) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint entry.type entry.value) s.vs_memory` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`0`, `val_footprint entry.type entry.value`] mp_tac) >> simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_footprint_frame >> simp[] >>
  qexistsl [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >> simp[] >> gvs[SUBSET_DEF]
QED

Theorem hash_ghost_inv_region_frame:
  !d cenv cx es G tn s ctx fn sa t G' tn'.
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n b k. local_region cenv es.scopes s n b k ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
    tn'.t_mem SUBSET tn.t_mem /\ stor_taint_ok cx tn' t ==>
    ghost_inv d cenv cx es G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
    ptr_covers G' tn' p t k` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> simp[]
QED

Resume hash_ghost_inv_region_frame[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
  drule_all hash_local_robust_region_frame >> simp[]
QED

Finalise hash_ghost_inv_region_frame

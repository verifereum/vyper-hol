(* Equal-layout aggregate stores copy dead bytes as well as live bytes.
   The exterior window, not global memory cleanliness, frames the ghost. *)
Theory bodyPtrMakeArrayFlatStore
Ancestors
  annAssignPtrScratch bodyPtrDefs context compileEnv exprSimProps
  venomState pred_set

Theorem literal_flat_store_counted:
  compile_store_memory ce (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  k = type_memory_bytes ce ty /\ k < dimword (:256) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\ val_footprint tv v <= k /\
  ptr_mem_ok cx ty v (Var src) G tn s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ghost_kept ce es fr G0 tn0 s0 G tn /\
  (!name p n i. local_region ce es.scopes s name p n /\
    p <= i /\ i < p+n ==> ~(w2n b <= i /\ i < w2n b+k)) /\
  (!aid p n i. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    aid < fr.cs_next_id /\ p <= i /\ i < p+n ==>
    ~(w2n b <= i /\ i < w2n b+k)) /\
  (!name p n i. local_region ce es.scopes s0 name p n /\
    p <= i /\ i < p+n ==> ~(w2n b <= i /\ i < w2n b+k)) ==>
  ?sf tf.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    ghost_inv d ce cx es G tf sf /\ ghost_kept ce es fr G0 tn0 s0 G tf /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers G tf p sf n) /\
    (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> gvs[compile_store_memory_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m` by
    (gvs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  drule_all annassign_counted_copy_robust_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule annassign_state_restore_elim_ptr >> disch_tac >>
  drule annassign_taint_restore_elim_ptr >> disch_tac >>
  `ghost_inv d ce cx es G tn' s'` by
    (qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `tn' = _` (fn th => once_rewrite_tac[th]) >>
     qpat_x_assum `s'.vs_memory = _` kall_tac >>
     irule annassign_ghost_exterior_ptr >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexists `{i | w2n b <= i /\ i < w2n b + type_memory_bytes ce ty}` >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ghost_kept ce es fr G0 tn0 s0 G tn'` by
    (irule annassign_ghost_kept_exterior_ptr >>
     qexistsl [`tn`, `{i | w2n b <= i /\ i < w2n b + type_memory_bytes ce ty}`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl [`s'`, `tn'`] >> simp[] >>
  rpt strip_tac >> irule annassign_coverage_var_frame_ptr >> metis_tac[]
QED

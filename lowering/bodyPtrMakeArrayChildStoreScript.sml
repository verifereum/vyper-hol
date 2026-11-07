(* Consume an actual child expression endpoint, not a second semantic run. *)
Theory bodyPtrMakeArrayChildStore
Ancestors
  bodyPtrMakeArrayFlatStore bodyPtrMakeArrayMemoryFrame
  abiDecodeStaticProps bodyPtrDefs loweringPosts exprSimProps
  context compileEnv venomState

Theorem literal_flat_child_store:
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) sa = ((),sb) /\
  expr_post ctx func ce cx e esi si sa s0 es' v op s /\
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  k = type_memory_bytes ce (lowered_value_type ce e) /\ 0 < k /\ k < dimword(:256) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_footprint tv v <= k /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok ce e op G s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s k /\
  stmt_state_rel ctx func ce cx es' s /\ ghost_inv d ce cx es' G tn s /\
  local_ptrs_reserved ce sa /\ ghost_kept ce es' fr G0 tn0 sf0 G tn /\
  (!name p n i. local_region ce es'.scopes s name p n /\
    p <= i /\ i < p+n ==> ~(w2n b <= i /\ i < w2n b+k)) /\
  (!aid p n i. FLOOKUP sf0.vs_allocas aid = SOME (p,n) /\
    aid < fr.cs_next_id /\ p <= i /\ i < p+n ==>
    ~(w2n b <= i /\ i < w2n b+k)) /\
  (!name p n i. local_region ce es'.scopes sf0 name p n /\
    p <= i /\ i < p+n ==> ~(w2n b <= i /\ i < w2n b+k)) /\
  val_wf pt pv /\ val_footprint pt pv <= psz /\
  (pp+psz <= w2n b \/ w2n b+k <= pp) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory pt pv pp m) ==>
  ?sf tf.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~sf.vs_halted /\ stmt_state_rel ctx func ce cx es' sf /\
    ghost_inv d ce cx es' G tf sf /\ ghost_kept ce es' fr G0 tn0 sf0 G tf /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers G tf p sf n) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==> val_in_memory tv v (w2n b) m) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==> val_in_memory pt pv pp m) /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x s) /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?w. eval_operand op s = SOME w` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_at_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `?src. op = Var src /\ lookup_var src s = SOME w /\ ptr_covers G tn src s k` by
    (gvs[ptr_buf_ok_def, ptr_val_ok_def, ptr_covers_def, eval_operand_def] >>
     metis_tac[]) >> pop_assum strip_assume_tac >> gnvs[] >>
  `ptr_mem_ok cx (expr_type e) v (Var src) G tn s` by gvs[ptr_val_ok_def] >>
  drule literal_flat_store_counted >>
  simp[arithmeticTheory.ADD_COMM] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`sf`, `tf`] >> simp[] >>
  rpt strip_tac >> irule robust_val_in_memory_shrinking_frame >>
  simp[] >> qexistsl [`tn.t_mem`, `tf.t_mem`, `s.vs_memory`, `sf.vs_memory`, `psz`] >>
  simp[] >> reverse conj_tac
  >- (irule mem_bytes_at_bytewise >> rpt strip_tac >>
      `~(w2n b <= i /\ i < w2n b + type_memory_bytes ce (expr_type e))` by decide_tac >>
      metis_tac[]) >>
  rpt strip_tac >>
  `~(w2n b <= i /\ i < w2n b + type_memory_bytes ce (expr_type e))` by decide_tac >>
  metis_tac[]
QED

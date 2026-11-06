(* Runtime-length bytestring copy with a protected exterior ghost frame. *)
Theory bodyPtrMakeArrayBytesStore
Ancestors
  annAssignPtrExterior annAssignPtrBytestring bodyPtrMakeArrayBytesTransport
  bodyPtrDefs context compileEnv exprSimProps venomState pred_set

Theorem literal_bytes_store_counted:
  compile_store_memory ce (Var src) (Var dst) ty sty sa = ((),sb) /\
  ~is_word_type ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ val_footprint tv v <= n /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * ((len + 31) DIV 32) /\ n < dimword (:256) /\
  ptr_mem_ok cx ty v (Var src) G tn s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ghost_kept ce es fr G0 tn0 s0 G tn /\ local_ptrs_reserved ce sa /\
  (!p. not_fresh_at fr p ==> not_fresh_at sa p) /\
  (!p k. ce.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. ce.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!name p k i. local_region ce es.scopes s name p k /\
    p <= i /\ i < p+k ==> ~(w2n b <= i /\ i < w2n b+n)) /\
  (!aid p k i. FLOOKUP s0.vs_allocas aid = SOME (p,k) /\
    aid < fr.cs_next_id /\ p <= i /\ i < p+k ==>
    ~(w2n b <= i /\ i < w2n b+n)) /\
  (!name p k i. local_region ce es.scopes s0 name p k /\
    p <= i /\ i < p+k ==> ~(w2n b <= i /\ i < w2n b+n)) ==>
  ?H tf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    ghost_inv d ce cx es H tf sf /\ ghost_kept ce es fr G0 tn0 s0 H tf /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
       ptr_covers H tf p sf k) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m` by
    (gvs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)` by
    metis_tac[robust_bytestring_source_live] >>
  drule_all annassign_bytestring_copy_robust_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `ghost_inv d ce cx es Gf tnf sf` by
    (irule annassign_ghost_vars_exterior_ptr >>
     qexistsl [`G`, `ctx`, `func`, `s`, `tn`,
               `{i | w2n b <= i /\ i < w2n b+n}`] >>
     simp[] >> metis_tac[local_ptrs_reserved_def, arithmeticTheory.ADD_COMM]) >>
  `ghost_kept ce es fr G0 tn0 s0 Gf tnf` by
    (irule annassign_ghost_kept_vars_exterior_ptr >>
     qexistsl [`G`, `tn`, `{i | w2n b <= i /\ i < w2n b+n}`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl [`Gf`, `tnf`, `sf`] >> simp[] >>
  rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED

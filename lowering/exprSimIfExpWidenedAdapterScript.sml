(* Physical owned values can be relocated without exposing allocation regions
   to expression consumers.  No expression syntax occurs in this boundary. *)
Theory exprSimIfExpWidenedAdapter
Ancestors
  exprSimIfExp exprSimHyps exprSimTypedAlloc valueEncodingTyping loweringPosts

Theorem normalize_owned_value_framed_frag:
  compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf, sm) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((), sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx sty origin sa es v src s /\
  expr_val_own ce cx sty origin sa es v src s /\
  ~is_word_type sty /\
  val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv /\
  eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory ==>
  frag_exec ctx sa sb (\z. z = s)
    (\u. ?w. stmt_state_rel ctx func ce cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) u.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w, type_memory_size dtv) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      (!name b len. local_region ce es.scopes s name b len ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len)) R
Proof
  strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all expr_val_at_bound >> simp[]) >>
  `?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\
    b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len` by
    (fs[expr_val_own_def] >>
     qpat_x_assum `!tv. evaluate_type _ sty = SOME tv ==> _`
       (qspec_then `stv` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 value_has_type_val_wf] >>
  drule compile_return_normalize_framed_frag >>
  disch_then irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`stv`, `sty`, `sw`, `src`] >> simp[] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `len`] >> simp[]
QED

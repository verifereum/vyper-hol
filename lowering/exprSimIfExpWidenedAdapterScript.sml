(* Physical owned values can be relocated without exposing allocation regions
   to expression consumers.  No expression syntax occurs in this boundary. *)
Theory exprSimIfExpWidenedAdapter
Ancestors
  exprSimIfExp exprSimHyps exprSimTypedAlloc valueEncodingTyping loweringPosts
  vyperTypeSystem valueEncodingProps vyperValue valueEncoding vyperMisc

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

Theorem ifexp_changed_aggregate_source:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') /\
  post_value_type ce e <> expr_type e /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  expr_post ctx func ce cx e es sa sb s0 es' v src s ==>
  ?stv dtv sw.
    type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_footprint stv v = type_memory_size stv /\
    0 < type_memory_size stv /\
    stmt_state_rel ctx func ce cx es' s /\
    expr_val_at ce cx (post_value_type ce e) sa sb es' v src s /\
    expr_val_own ce cx (post_value_type ce e) sa sb es' v src s /\
    eval_operand src s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory
Proof
  strip_tac >>
  `(!sty dty. arg_type_fits sty dty ==>
      !tenv stv. evaluate_type tenv sty = SOME stv /\
        type_memory_size stv = 0 ==> sty = dty) /\
   (!stys dtys. arg_types_fit stys dtys ==>
      !tenv stvs. OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
        type_memory_size_list stvs = 0 ==> stys = dtys)` by
    (ho_match_mp_tac arg_type_fits_ind >>
     rw[arg_type_fits_def] >>
     gvs[evaluate_type_def, evaluate_types_OPT_MMAP, listTheory.OPT_MMAP_def,
         AllCaseEqs(), type_memory_size_def] >>
     metis_tac[cj 1 type_memory_size_pos]) >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    (spose_not_then assume_tac >>
     `post_value_type ce e = expr_type e` by
       (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
  gvs[] >>
  `~is_word_type ty /\ ~is_bytestring_type ty` by
    metis_tac[post_value_type_word, post_value_type_bytestring,
              vyperASTTheory.expr_type_def] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  `0 < type_memory_size stv` by
    (gvs[type_widens_to_def] >> metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `val_footprint stv v = type_memory_size stv` by
    (qpat_x_assum `evaluate_type _ (lowered_value_type _ _) = _` mp_tac >>
     qpat_x_assum `~is_bytestring_type (lowered_value_type _ _)` mp_tac >>
     qmatch_goalsub_abbrev_tac `evaluate_type tenv sty` >>
     Cases_on `sty` >>
     simp[compileEnvTheory.is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> Cases_on `v` >>
     gvs[val_footprint_def] >>
     gvs[compileEnvTheory.is_bytestring_type_def]) >>
  gvs[expr_post_def, expr_val_rel_def] >>
  gvs[vyperASTTheory.expr_type_def]
QED

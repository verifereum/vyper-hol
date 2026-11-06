(* Semantic annotation resources for the reason literal shortcut. *)
Theory reasonLiteralPostPtr
Ancestors reasonLiteralBufferPtr reasonMemorySuccessPtr reasonResourcesPtr
  exprSimPtrLiteralBuffer compileEnv words freshWrites venomState
  venomExecSemantics context ptrDiscipline
  exprSimHyps exprSimHypsDefs vyperTypeSystem allocLimits vyperAST
  vyperValue bodyPtrDefs

Theorem reason_literal_source_bounds:
  expr_body_pre cenv cx env
    (Literal (BaseT (StringT ml)) (StringL str)) es ==>
  LENGTH str <= ml /\ type_alloc_ok cenv (BaseT (StringT ml)) /\
  64 + type_memory_bytes cenv (BaseT (StringT ml)) < dimword (:256)
Proof
  strip_tac >>
  `LENGTH str <= ml /\ type_alloc_ok cenv (BaseT (StringT ml))` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
        alloc_limits_expr_def] >>
  drule reason_encoder_allocation_limit >> simp[]
QED

Theorem reason_literal_string_representation:
  LENGTH str <= ml /\
  mem_word_at b s.vs_memory = n2w (LENGTH str) /\
  mem_bytes_at (b+32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
  tn'.t_mem = (tn.t_mem UNION dirty) DIFF
    {i | b <= i /\ i < b+32+32*word_size (LENGTH str)} ==>
  val_wf (BaseTV (StringT ml)) (StringV str) /\
  val_in_memory (BaseTV (StringT ml)) (StringV str) b s.vs_memory /\
  val_footprint (BaseTV (StringT ml)) (StringV str) <= 32+32*word_size (LENGTH str) /\
  (!i. b <= i /\ i < b+val_footprint (BaseTV (StringT ml)) (StringV str) ==>
    i NOTIN tn'.t_mem) /\
  val_store_size (BaseTV (StringT ml)) (StringV str) = 32+32*word_size (LENGTH str)
Proof
  strip_tac >> irule literal_ptr_string_representation >> simp[] >>
  qexists_tac `tn with t_mem := tn.t_mem UNION dirty` >> simp[]
QED

Theorem reason_literal_type_evaluates:
  expr_body_pre cenv cx env
    (Literal (BaseT (StringT ml)) (StringL str)) es ==>
  evaluate_type (get_tenv cx) (BaseT (StringT ml)) = SOME (BaseTV (StringT ml))
Proof
  strip_tac >> drule expr_body_pre_type_evaluates >>
  simp[expr_type_def, evaluate_type_def] >> metis_tac[]
QED

Theorem reason_literal_string_ptr_val:
  LENGTH str <= ml /\
  lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,32+32*word_size ml) /\
  op_taint tn' (Var p) = {} /\ b+32+32*word_size ml < dimword (:256) /\
  mem_word_at b s.vs_memory = n2w (LENGTH str) /\
  mem_bytes_at (b+32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
  tn'.t_mem = (tn.t_mem UNION dirty) DIFF
    {i | b <= i /\ i < b+32+32*word_size (LENGTH str)} ==>
  ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) G tn' s
Proof
  strip_tac >> drule_all reason_literal_string_representation >> strip_tac >>
  simp[ptr_val_ok_def, is_word_type_def] >>
  irule literal_clean_ptr_mem_ok >> simp[] >>
  `b < dimword (:256)` by decide_tac >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  simp[wordsTheory.w2n_n2w, evaluate_type_def] >> rpt strip_tac >>
  gvs[] >> decide_tac
QED


Theorem reason_literal_memory_vv_frame_post:
  evaluate_type (get_tenv cx) (BaseT (StringT ml)) = SOME (BaseTV (StringT ml)) /\
  val_wf (BaseTV (StringT ml)) (StringV str) /\
  val_in_memory (BaseTV (StringT ml)) (StringV str) b t.vs_memory /\
  val_footprint (BaseTV (StringT ml)) (StringV str) <= 32+32*word_size ml /\
  LENGTH str <= ml /\ b < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
  u.vs_memory = s.vs_memory /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b (32+32*word_size ml) a len) /\
  (!a len. a+len <= b \/ b+32+32*word_size (LENGTH str) <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size ml))] [p])
    (fn_insts func) /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size ml) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint b (32+32*word_size ml) a len) /\
  buf.buf_operand = Var p /\ lookup_var p t = SOME (n2w b) /\
  sa.cs_next_id < sb.cs_next_id ==>
  vv_post ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
    es sa sb s es (Value (StringV str))
    (LocatedValue (BaseT (StringT ml)) (base_ptr buf))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  `eval_operand buf.buf_operand t = SOME (n2w b)` by
    simp[eval_operand_def] >>
  drule_at (Pat `eval_operand _ _ = _`)
    (Q.INST [`e` |-> `Literal (BaseT (StringT ml)) (StringL str)`]
      literal_ptr_memory_vv_frame_post) >>
  disch_then (irule o REWRITE_RULE [expr_type_def]) >>
  simp[is_word_type_def, w2n_n2w] >>
  qexistsl_tac [`32+32*word_size ml`, `p`, `sh`, `u`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
      simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _`
    (qspecl_then [`a`, `len`] mp_tac) >>
  simp[] >> disch_then irule >> decide_tac
QED

Theorem reason_literal_post_compiler:
  compile_bytelike_literal bs ml sa = (buf,sb) /\ fn_has_code sa sb func /\
  buf.buf_operand = Var p ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size ml))] [p])
    (fn_insts func) /\ sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule reason_literal_compiler_shape >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by gvs[] >>
  conj_tac
  >- (irule exprSimHashTheory.hash_emitted_inst_mem >>
      goal_assum (drule_at Any) >> simp[]) >>
  decide_tac
QED

Theorem reason_literal_buffer_source_post:
  compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf,sb) /\
  expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+32*word_size ml < dimword (:256) ==>
  ?t p G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    buf.buf_operand = Var p /\
    expr_post ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
      es sa sb s es (StringV str) (Var p)
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) G' tn'
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule reason_literal_source_bounds >> strip_tac >>
  `LENGTH (MAP (n2w o ORD) str : word8 list) <= ml` by simp[] >>
  drule_all reason_literal_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `func`, `PG`, `G`, `D`]
    (strip_assume_tac o REWRITE_RULE [listTheory.LENGTH_MAP])) >>
  drule_all reason_literal_post_compiler >> strip_tac >>
  drule reason_literal_type_evaluates >> strip_tac >>
  drule_all reason_literal_string_representation >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  qexistsl_tac [`t`, `p`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "post" >> suspend "ptr"
QED

Resume reason_literal_buffer_source_post[post]:
  `val_footprint (BaseTV (StringT ml)) (StringV str) <= 32+32*word_size ml`
    by decide_tac >>
  `vv_post ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
    es sa sb s es (Value (StringV str))
    (LocatedValue (BaseT (StringT ml)) (base_ptr buf))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule reason_literal_memory_vv_frame_post >> asm_rewrite_tac[] >>
     qexistsl_tac [`b`, `p`, `sh`, `u`] >> asm_rewrite_tac[]) >>
  drule exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory >>
  simp[base_ptr_def, is_word_type_def]
QED

Resume reason_literal_buffer_source_post[ptr]:
  irule reason_literal_string_ptr_val >> asm_rewrite_tac[] >>
  qexistsl_tac [`b`, `dirty`, `tn`] >>
  asm_rewrite_tac[] >> simp[NoAsms, lookup_var_def] >>
  qpat_x_assum `lookup_var p t = _` mp_tac >>
  simp[NoAsms, lookup_var_def] >> asm_rewrite_tac[]
QED

Finalise reason_literal_buffer_source_post

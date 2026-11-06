Theory bodyPtrIfExpBytesEndpoint
Ancestors
  bodyPtrIfExpBytesSemantic bodyPtrIfExpBytesCallerFrame bodyPtrIfExpBytesPost
  bodyPtrIfExpBytesResources bodyPtrDefs exprSimProps loweringPosts compileEnv
  venomState finite_map words exprSimBufferStore exprSimDefs exprLoweringProps

Theorem ifexp_bytes_destination_expr_post:
  vv_post ctx fn ce cx arm es sa sc s0 ee raw vv t /\
  stmt_state_rel ctx fn ce cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sc /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\
  MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [out]) (fn_insts fn) /\
  not_local_ptr ce ee.scopes out /\ n <= capacity /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,capacity) /\
  sa.cs_next_id <= aid /\ aid < sd.cs_next_id /\
  (sf with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = t /\
  sf.vs_memory = (mcopy (w2n w) a n t).vs_memory /\
  (!x. not_fresh_at sc x ==> lookup_var x sf = lookup_var x t) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n w \/ w2n w+capacity <= off) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= w2n w \/ w2n w+capacity <= p) /\
  evaluate_type (get_tenv cx) (expr_type result) = SOME dtv /\
  ~is_word_type (expr_type result) /\ val_wf dtv v /\
  val_footprint dtv v <= capacity /\
  eval_operand (Var out) sf = SOME w /\
  val_in_memory dtv v (w2n w) sf.vs_memory ==>
  expr_post ctx fn ce cx result es sa sd s0 ee v (Var out) sf
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee t` by gvs[vv_post_def] >>
  `stmt_state_rel ctx fn ce cx ee sf` by
    (drule_all ifexp_bytes_mcopy_semantic_state >> simp[]) >>
  `sf.vs_allocas = t.vs_allocas` by
    gvs[venom_state_component_equality] >>
  `!off len. off+len <= w2n w \/ w2n w+n <= off ==>
     mem_bytes_at off len sf.vs_memory = mem_bytes_at off len t.vs_memory` by
    (rpt strip_tac >> simp[] >> irule buffer_mcopy_exterior >> simp[]) >>
  drule_all ifexp_bytes_original_semantic_frame >> strip_tac >>
  `expr_val_at ce cx (expr_type result) sa sd ee v (Var out) sf` by
    (irule ifexp_allocated_destination_placement >>
     qexistsl_tac [`aid`, `capacity`, `dtv`, `w`] >> simp[] >>
     rpt strip_tac >>
     `local_region ce es.scopes s0 name p sz` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `fn` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sa`, `ee.scopes`, `sf`] >> simp[]) >>
     qpat_x_assum `!name p sz. local_region ce es.scopes s0 name p sz ==> _` drule >>
     simp[arithmeticTheory.ADD_COMM]) >>
  simp[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem ifexp_bytes_destination_ptr_post:
  ptr_covers G tn out sf capacity /\
  evaluate_type (get_tenv cx) (expr_type result) = SOME dtv /\
  ~is_word_type (expr_type result) /\
  val_store_size dtv v <= capacity /\
  type_memory_bytes ce (lowered_value_type ce result) <= capacity /\
  eval_operand (Var out) sf = SOME w /\
  (!m. mem_agree_outside tn.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n w) m) ==>
  ptr_val_ok cx (expr_type result) v (Var out) G tn sf /\
  ptr_buf_ok ce result (Var out) G sf
Proof
  strip_tac >>
  gvs[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
      eval_operand_def] >> conj_tac >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`b`, `sz'`] >> simp[] >> decide_tac
QED

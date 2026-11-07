(* Turn the loop's robust memory and allocation coverage into the public
   pointer value/buffer posts.  Capacity is distinct from value footprint. *)
Theory bodyPtrMakeArrayPackage
Ancestors
  bodyPtrMakeArrayTupleLoop bodyPtrDefs exprSimProps valueEncoding
  venomState words ptrDiscipline bodyPtrMakeArrayAllocCursor
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayMaterialiseFrame
  bodyPtrMakeArrayExternalInstall loweringPosts exprSimAlloc emitHelperProps
  finite_map bodyPtrMakeArrayConsInvariant allocationPtr compileEnv

Theorem literal_memory_ptr_posts:
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_wf tv v /\ type_memory_size tv <= capacity /\
  type_memory_bytes ce (lowered_value_type ce e) <= capacity /\
  lookup_var root s = SOME (n2w addr) /\ addr < dimword(:256) /\
  FLOOKUP G root = SOME (addr,capacity) /\ op_taint tn (Var root) = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v addr m) ==>
  ptr_val_ok cx ty v (Var root) G tn s /\ ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  `val_store_size tv v <= capacity` by metis_tac[val_store_size_le, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, eval_operand_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.ADD_ASSOC]
QED

Theorem literal_allocated_loop_start:
  compile_alloc_buffer capacity sa = (buf,sm) /\ buf.buf_operand = Var root /\
  cs_extends sm sb /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  capacity < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?a H tm addr.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK a) /\
    literal_loop_frame ctx func ce cx d root sa.cs_next_id addr capacity
      es sa s G tn es sm H tm a [] 0
Proof
  strip_tac >> drule_all allocated_fragment_install >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all (SRULE [] literal_alloc_buffer_cursor_run) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule literal_alloc_buffer_cursor_shape >> strip_tac >>
  `ghost_inv d ce cx es H tm a /\ ghost_kept ce es sa G tn s H tm` by
    (irule literal_allocated_copy_ghost_post >> simp[op_prov_def] >>
     conj_tac >- gvs[op_prov_def] >>
     conj_tac >- (qexistsl [`w2n w`, `capacity`, `a`] >> simp[arithmeticTheory.ADD_COMM] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- metis_tac[] >>
       qpat_x_assum `!i. _ ==> (i IN tm.t_mem <=> _)` mp_tac >>
       simp[arithmeticTheory.ADD_COMM]) >>
     metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      pairTheory.SND, exprLoweringPropsTheory.ci_mono_def] >>
  `!name b len. local_region ce es.scopes s name b len ==>
     regions_disjoint (w2n w) capacity b len` by
    metis_tac[exprSimPtrLiteralBufferTheory.literal_ptr_local_region_frame] >>
  qexistsl [`a`, `H`, `tm`, `w2n w`] >> simp[] >>
  gvs[literal_loop_frame_def, wb_frame_def, locals_kept_def,
    regions_disjoint_def, eval_operand_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem literal_loop_vv_post:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s0 G0 tn0 ee sb G tn s cells off /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ val_wf tv v /\
  val_footprint tv v <= capacity /\ addr < dimword(:256) /\
  val_in_memory tv v addr s.vs_memory ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) s
Proof
  strip_tac >>
  fs[literal_loop_frame_def] >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, contextTheory.mk_ptr_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    eval_operand_def] >>
  reverse conj_tac >- (fs[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexistsl [`aid`, `addr`, `capacity`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name p k. local_region ce ee.scopes s name p k ==> _`
    (drule_then mp_tac) >> decide_tac
QED

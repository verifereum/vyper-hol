Theory bodyPtrIfExpBytesEndpoint
Ancestors
  bodyPtrIfExpBytesSemantic bodyPtrIfExpBytesCallerFrame bodyPtrIfExpBytesPost
  bodyPtrIfExpBytesResources bodyPtrDefs exprSimProps loweringPosts compileEnv loweringStateRelDefs
  venomState finite_map words exprSimBufferStore exprSimDefs exprLoweringProps
  ghostPcTransportPtr bodyPtrIfExpAllocSource stmtFragPtr

Theorem ifexp_bytes_destination_expr_post:
  post_value_type ce result = expr_type result /\
  vv_post ctx fn ce cx arm es sa sc s0 ee raw vv t /\
  (~expr_has_effect result ==> ~expr_has_effect arm) /\
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
  expr_post ctx fn ce cx result es sa sd s0 ee v (Var out) sf /\
  (~expr_has_effect arm ==> pure_frame ce fn es sa s0 sf)
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
  `~expr_has_effect arm ==> pure_frame ce fn es sa s0 sf` by
    (strip_tac >>
     `pure_frame ce fn es sa s0 t` by
       (qpat_assum `vv_post _ _ _ _ arm _ _ _ _ _ _ _ _`
          (mp_tac o REWRITE_RULE [vv_post_def]) >>
        strip_tac >> qpat_x_assum `~expr_has_effect arm ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     match_mp_tac pure_frame_buffer_tail >>
     qexistsl_tac [`t`, `mk_inst aid ALLOCA [Lit (n2w capacity)] [out]`,
                   `w2n w`, `capacity`] >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `sf.vs_allocas = _` (fn th => rewrite_tac[th]) >> simp[])
     >- first_assum ACCEPT_TAC
     >- simp[venomInstTheory.mk_inst_def]
     >- simp[venomInstTheory.mk_inst_def]
     >- (qpat_assum `sf.vs_allocas = _` (fn th => rewrite_tac[th]) >>
         simp[venomInstTheory.mk_inst_def] >> first_assum ACCEPT_TAC)
     >- (rpt strip_tac >>
         qpat_assum `!name p sz. local_region ce es.scopes s0 name p sz ==> _` drule >>
         simp[regions_disjoint_def] >> decide_tac) >>
     rpt gen_tac >> rewrite_tac[regions_disjoint_def] >> strip_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len sf.vs_memory = _` irule >>
     decide_tac) >>
  `~expr_has_effect result ==> pure_frame ce fn es sa s0 sf` by
    (strip_tac >> qpat_x_assum `~expr_has_effect arm ==> _` irule >>
     qpat_x_assum `_ ==> ~expr_has_effect arm` irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- (simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
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

Theorem ifexp_expr_post_inst_idx[simp]:
  expr_post ctx fn ce cx e es sa sb s0 ee v op (s with vs_inst_idx := k) <=>
  expr_post ctx fn ce cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, lookup_var_def, local_region_def]
QED

Theorem ifexp_pointer_post_inst_idx[simp]:
  ptr_val_ok cx ty v op G tn (s with vs_inst_idx := k) <=>
  ptr_val_ok cx ty v op G tn s
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def]
QED

Theorem ifexp_ghost_inv_inst_idx[simp]:
  ghost_inv d ce cx ee G tn (s with vs_inst_idx := k) <=>
  ghost_inv d ce cx ee G tn s
Proof
  mp_tac (Q.INST [`p` |-> `s.vs_prev_bb`, `l` |-> `s.vs_current_bb`,
                   `i` |-> `k`, `cenv` |-> `ce`, `es` |-> `ee`] ghost_inv_jump_to) >>
  `s with <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
             vs_inst_idx := k|> = s with vs_inst_idx := k` by
    simp[venom_state_component_equality] >> simp[]
QED

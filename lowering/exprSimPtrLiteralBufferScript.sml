(* Robust literal representations and ghost frame boundaries. *)
Theory exprSimPtrLiteralBuffer
Ancestors
  exprSimPtrLiteralPayload exprSimLiteralBuffer allocationPtr exprLowering
  context emitHelper freshWrites vfmConstants loweringHalt
  exprSimPtrLiteralChunks robustCopyTransportPtr exprSimProps
  bodyPtrDefs compileEnv valueEncoding valueEncodingProofs valueEncodingProps
  venomMemProofs venomState finite_map words list pred_set
  exprSimPtrLiteralOps venomExecSemantics venomInst fragExecPtr fragExec fragGasSeqPtr exprLoweringProps ptrDiscipline instIdxIndep

Theorem literal_clean_window_agree:
  mem_agree_outside dirty mem mem' /\
  (!i. off <= i /\ i < off+len ==> i NOTIN dirty) ==>
  mem_bytes_at off len mem = mem_bytes_at off len mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < len` >>
  `off+j NOTIN dirty` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (off+j) 1 mem = mem_bytes_at (off+j) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem literal_clean_representation_robust:
  val_in_memory tv value off mem /\ val_wf tv value /\
  (!i. off <= i /\ i < off+val_footprint tv value ==> i NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==>
    val_in_memory tv value off mem'
Proof
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  conj_tac >- simp[] >>
  qexists_tac `mem` >> simp[] >>
  irule literal_clean_window_agree >> metis_tac[]
QED

Theorem literal_ghost_kept:
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem literal_clean_ptr_mem_ok:
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME (base_addr,sz) /\
  base_addr <= w2n w /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    val_wf tv value /\ val_in_memory tv value (w2n w) s.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv value ==>
         i NOTIN tn.t_mem) /\
    w2n w + val_store_size tv value <= base_addr + sz) ==>
  ptr_mem_ok cx ty value (Var p) G tn s
Proof
  strip_tac >> simp[ptr_mem_ok_def, eval_operand_def] >>
  rpt strip_tac
  >- (irule literal_clean_representation_robust >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`tn.t_mem`, `s.vs_memory`] >> metis_tac[]) >>
  qexistsl_tac [`base_addr`, `sz`] >> metis_tac[]
QED

Theorem literal_site_ptr_buf_ok:
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME (base_addr,sz) /\
  base_addr <= w2n w /\
  w2n w + type_memory_bytes cenv (lowered_value_type cenv e) <= base_addr + sz ==>
  ptr_buf_ok cenv e (Var p) G s
Proof
  simp[ptr_buf_ok_def, eval_operand_def] >> metis_tac[]
QED

Theorem literal_ghost_inv_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x s' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
         i NOTIN writes)) /\
  (!i. i NOTIN writes ==>
    mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' s'
Proof
  strip_tac >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
          ptr_covers G' tn' x s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_def, stor_taint_ok_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`,
                     `tn'.t_mem`, `writes`] >>
      metis_tac[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem literal_header_chunks_ptr:
  compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
  not_fresh_at sh p /\ lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,32+32*word_size (LENGTH bs)) /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  b + 32 + 32*word_size (LENGTH bs) < dimword (:256) ==>
  ?t G' tn'.
    run_inst_seq (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb) s G' tn' /\
    tn'.t_mem = tn.t_mem DIFF
      {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sh v ==>
      FLOOKUP G' v = FLOOKUP G v /\
      FLOOKUP tn'.t_var v = FLOOKUP tn.t_var v)
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn p s 32` by
    (simp[ptr_covers_def, w2n_n2w] >> decide_tac) >>
  `step_inst_base (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] []) s =
     OK (mstore b (n2w (LENGTH bs)) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
  drule literal_mstore_ghost >>
  disch_then (qspecl_then [`n2w (LENGTH bs)`, `tn`, `id`, `PG`, `G`]
    strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `lookup_var p u = SOME (n2w b)` by
    simp[Abbr `u`, mstore_def, lookup_var_def] >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `th = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `lookup_var p uh = SOME (n2w b) /\ op_taint th (Var p) = {}` by
    (simp[Abbr `uh`, Abbr `th`, lookup_var_def, op_taint_def] >>
     fs[lookup_var_def, op_taint_def]) >>
  `?t G' tn'. run_inst_seq (emitted_insts sh sb) uh = OK t /\
    inst_seq_ptr D 0 ctx fn PG G th (emitted_insts sh sb) uh G' tn' /\
    tn'.t_mem = th.t_mem DIFF
      {i | b+32 <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = th.t_stor /\ tn'.t_trans = th.t_trans /\
    tn'.t_imm = th.t_imm /\
    (!v. not_fresh_at sh v ==> lookup_var v t = lookup_var v uh /\
      FLOOKUP G' v = FLOOKUP G v /\ FLOOKUP tn'.t_var v = FLOOKUP th.t_var v)` by
    (irule (cj 6 literal_chunks_ptr) >>
     simp[] >>
     qexistsl_tac [`b`, `32+32*word_size (LENGTH bs)`, `p`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sb)` by
    metis_tac[cj 5 literal_chunks_ptr, arithmeticTheory.LESS_EQ_REFL,
              arithmeticTheory.ADD_ASSOC] >>
  Cases_on `run_inst_seq (emitted_insts sh sb) u` >>
  fs[Abbr `uh`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qexistsl_tac [`v`, `G'`, `tn'`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, literal_mstore_ptr_inst_ok] >>
  gvs[Abbr `u`, Abbr `th`, w2n_n2w, mk_inst_def,
      arithmeticTheory.LESS_MOD, is_terminator_def] >>
  rpt conj_tac >> simp[] >>
  simp[pred_setTheory.EXTENSION] >> rpt gen_tac >>
  eq_tac >> simp[] >> decide_tac
QED

Theorem literal_ptr_bytelike_alloca_mem:
  !bs sa buf sb func.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    fn_has_code sa sb func ==>
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32 + 32 * word_size (LENGTH bs)))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     GSYM vfmConstantsTheory.word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u,sb)` >> Cases_on `u` >>
  drule literal_payload_chunks_shape >> strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      same_blocks_def] >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` kall_tac >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >>
  goal_assum (drule_at Any) >> simp[MEM_APPEND]
QED

Theorem literal_ptr_buffer_prefix_shape:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit value] sm = ((),sh) ==>
  ?p. p = STRING #"%" (toString sa.cs_next_var) /\
    buf.buf_operand = Var p /\ ~not_fresh_at sa p /\
    not_fresh_at sm p /\ not_fresh_at sh p /\
    emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] /\
    emitted_insts sm sh = [mk_inst sm.cs_next_id MSTORE [Var p; Lit value] []] /\
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
    same_blocks sa sm /\ same_blocks sm sh /\
    sm.cs_next_var = sa.cs_next_var+1 /\ sh.cs_next_var = sm.cs_next_var /\
    sm.cs_next_id = sa.cs_next_id+1 /\ sh.cs_next_id = sm.cs_next_id+1
Proof
  strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def,
      emitted_insts_def, same_blocks_def, rich_listTheory.DROP_APPEND1,
      not_fresh_at_def] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  simp[not_fresh_at_def]
QED

Theorem literal_ptr_alloca_ghost:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?b dirty. FLOOKUP s1.vs_allocas id = SOME (b,n) /\
    b+n < dimword (:256) /\ lookup_var out s1 = SOME (n2w b) /\
    step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 =
      G |+ (out,(b,n)) /\
    step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn =
      tn with <|t_var := tn.t_var |+ (out,{}); t_mem := tn.t_mem UNION dirty|> /\
    dirty SUBSET {i | b <= i /\ i < b+n}
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule_all fresh_alloca_ghost >> strip_tac >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
      qexistsl_tac [`s.vs_alloca_next`,
        `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}`] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  qexists_tac `{}` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, taint_component_equality]
QED


Theorem literal_ptr_bytelike_shape:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) ==>
  ?sm sh p.
    compile_alloc_buffer (32+32*word_size (LENGTH bs)) sa = (buf,sm) /\
    emit_void MSTORE [Var p; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
    compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
    buf.buf_operand = Var p /\ p = STRING #"%" (toString sa.cs_next_var) /\
    ~not_fresh_at sa p /\ not_fresh_at sm p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    emitted_insts sa sm =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]] /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size (LENGTH bs)))] [p];
       mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] []] ++
      emitted_insts sh sb /\
    sa.cs_next_id < sm.cs_next_id /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb)
Proof
  strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     GSYM word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `emit_void MSTORE _ sm = (u,sh)` >> Cases_on `u` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u,sb)` >> Cases_on `u` >>
  drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
  drule literal_payload_chunks_shape >> strip_tac >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    (irule emitted_insts_append >> simp[] >> metis_tac[same_blocks_trans]) >>
  gvs[] >> conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem literal_bytelike_ptr_run:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+32*word_size (LENGTH bs) < dimword (:256) ==>
  ?u t b p sh G' tn'.
    buf.buf_operand = Var p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    stmt_state_rel ctx func cenv cx es u /\ u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size (LENGTH bs)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b (32+32*word_size (LENGTH bs)) a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b (32+32*word_size (LENGTH bs)) a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_labels = s.vs_labels /\ wb_frame cenv es es sa s u /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
    (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    FLOOKUP G' p = SOME (b,32+32*word_size (LENGTH bs)) /\
    lookup_var p t = SOME (n2w b) /\ op_taint tn' (Var p) = {} /\
    b+32+32*word_size (LENGTH bs) < dimword (:256) /\
    mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule literal_ptr_bytelike_shape >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size (LENGTH bs)))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[literal_ptr_bytelike_alloca_mem] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) (fn_insts func)` by metis_tac[] >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  suspend "payload"
QED

Resume literal_bytelike_ptr_run[payload]:
  qpat_x_assum `p = STRING _ _` kall_tac >>
  `w2n w = b` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `FLOOKUP u.vs_allocas _ = SOME (w2n w,_)` kall_tac >>
  qabbrev_tac `Ga = G |+ (p,(b,32+32*word_size (LENGTH bs)))` >>
  qabbrev_tac `ta = tn with <|t_var := tn.t_var |+ (p,{}); t_mem := tn.t_mem UNION dirty|>` >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var p uh = SOME (n2w b) /\
   FLOOKUP Ga p = SOME (b,32+32*word_size (LENGTH bs)) /\
   op_taint ta (Var p) = {}` by
    (simp[Abbr `uh`, Abbr `Ga`, Abbr `ta`, lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     metis_tac[lookup_var_def]) >>
  `b+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  `?t G' tn'.
    run_inst_seq (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) uh = OK t /\
    inst_seq_ptr D 0 ctx fn PG Ga ta
      (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb) uh G' tn' /\
    tn'.t_mem = ta.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = ta.t_stor /\ tn'.t_trans = ta.t_trans /\ tn'.t_imm = ta.t_imm /\
    (!v. not_fresh_at sh v ==> FLOOKUP G' v = FLOOKUP Ga v /\
      FLOOKUP tn'.t_var v = FLOOKUP ta.t_var v)` by
    (irule literal_header_chunks_ptr >> simp[] >> metis_tac[]) >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`u`, `SUC s.vs_inst_idx`] assume_tac) >>
  Cases_on `run_inst_seq
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) u` >>
  fs[Abbr `uh`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `b+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  qpat_x_assum `run_inst_seq _ (u with vs_inst_idx := _) = _` kall_tac >>
  qpat_x_assum `lookup_var p (u with vs_inst_idx := _) = _` kall_tac >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  suspend "assemble"
QED

Resume literal_bytelike_ptr_run[assemble]:
  qexistsl_tac [`u`, `v`, `b`, `sh`, `G'`, `tn'`] >>
  simp[] >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[run_inst_seq_def] >>
      asm_simp_tac bool_ss [] >> simp[mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[inst_seq_ptr_def] >>
      asm_simp_tac bool_ss [] >> simp[literal_alloca_ptr_inst_ok]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qpat_x_assum `v with <|vs_vars := _; vs_memory := _|> = u` mp_tac >> simp[]) >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (qpat_x_assum `!v. not_fresh_at sh v ==> _` (qspec_then `p` mp_tac) >>
      simp[op_taint_def, Abbr `ta`, FLOOKUP_UPDATE]) >>
  simp[Abbr `ta`, Abbr `Ga`] >>
  conj_tac
  >- (qpat_x_assum `dirty SUBSET _` mp_tac >> SET_TAC[]) >>
  rpt strip_tac >> `x <> p` by metis_tac[] >> simp[FLOOKUP_UPDATE]
QED

Finalise literal_bytelike_ptr_run

(* Ordinary transport across the fully written buffer. *)
Theorem literal_ptr_state_memory_frame:
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  (!a len. a+len <= b \/ b+n <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
  FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >> irule literal_state_memory_frame >>
  qexists_tac `u` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` irule >>
      qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      rename1 `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var lp) _)` >>
      `not_fresh_at sa lp` by metis_tac[local_ptrs_reserved_def] >>
      qpat_x_assum `!x. not_fresh_at sh x ==> _` irule >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >> strip_tac >>
      qpat_x_assum `!x. not_fresh_at sh x ==> _` irule >> metis_tac[]) >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) b n` by
    (qpat_x_assum `stmt_state_rel ctx _ _ _ _ u` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> regions_disjoint _ _ b sz` irule >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` irule >>
  gvs[regions_disjoint_def] >> decide_tac
QED

(* Public counterpart of S1's local post constructor. *)
Theorem literal_ptr_memory_vv_post:
  !func cenv cx e es sa sb s0 t v tvt buf w sz ctx.
    ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tvt v <= sz /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) ==>
    vv_post ctx func cenv cx e es sa sb s0 es (Value v)
      (LocatedValue (expr_type e) (base_ptr buf))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es es s0 t` by
    (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` kall_tac >>
  simp[loweringPostsTheory.vv_post_def, stmt_state_rel_inst_idx,
       loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def, base_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       eval_operand_def, lookup_var_def] >>
  qpat_assum `post_value_type _ _ = _` (fn th => simp[th]) >>
  `eval_operand buf.buf_operand (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w` by
    (Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  conj_tac
  >- (disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `sz`] >>
      simp[] >> rpt strip_tac >>
      `local_region cenv es.scopes t n lb lsz` by
        gvs[local_region_def, lookup_var_def] >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _`
        drule >> simp[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem literal_ptr_local_footprint_exterior:
  stmt_state_rel ctx func cenv cx es s /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN {i | b <= i /\ i < b+n})
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  conj_tac >- simp[] >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED

Theorem literal_ptr_ghost_frame:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    lookup_var x t = lookup_var x u /\ FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  u.vs_memory = s.vs_memory /\
  (!a len. a+len <= b \/ b+n <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+n} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[op_taint_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (irule literal_ghost_kept >> simp[] >> SET_TAC[]) >>
  irule literal_ghost_inv_frame >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+n}`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p u = SOME w` by metis_tac[] >>
      drule_all literal_ptr_local_footprint_exterior >>
      simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
  simp[] >> disch_then irule >> decide_tac
QED

Theorem literal_ptr_bytes_representation:
  LENGTH bs <= n /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} ==>
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) b s.vs_memory /\
  val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) <= 32+32*word_size (LENGTH bs) /\
  (!i. b <= i /\ i < b+val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) ==>
    i NOTIN tn'.t_mem) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV bs) = 32+32*word_size (LENGTH bs)
Proof
  strip_tac >>
  assume_tac (Q.SPEC `n` le_word_size_mul) >>
  assume_tac (Q.SPEC `LENGTH (bs:word8 list)` le_word_size_mul) >>
  simp[loweringPostsTheory.val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def, type_memory_size_def,
       vyperValueTheory.compatible_bound_def] >>
  rpt strip_tac >> simp[] >> decide_tac
QED

Theorem literal_ptr_string_representation:
  LENGTH str <= n /\
  mem_word_at b s.vs_memory = n2w (LENGTH str) /\
  mem_bytes_at (b+32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
  tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH str)} ==>
  val_wf (BaseTV (StringT n)) (StringV str) /\
  val_in_memory (BaseTV (StringT n)) (StringV str) b s.vs_memory /\
  val_footprint (BaseTV (StringT n)) (StringV str) <= 32+32*word_size (LENGTH str) /\
  (!i. b <= i /\ i < b+val_footprint (BaseTV (StringT n)) (StringV str) ==>
    i NOTIN tn'.t_mem) /\
  val_store_size (BaseTV (StringT n)) (StringV str) = 32+32*word_size (LENGTH str)
Proof
  strip_tac >>
  assume_tac (Q.SPEC `n` le_word_size_mul) >>
  assume_tac (Q.SPEC `LENGTH (str:string)` le_word_size_mul) >>
  simp[loweringPostsTheory.val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def, type_memory_size_def] >>
  rpt strip_tac >> simp[] >> decide_tac
QED

Theorem literal_ptr_local_region_frame:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  !name a len. local_region cenv scopes t name a len <=>
    local_region cenv scopes s name a len
Proof
  simp[local_region_def] >> rpt strip_tac >> eq_tac >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem literal_ptr_memory_vv_frame_post:
  ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
  val_footprint tv v <= n /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
  u.vs_memory = s.vs_memory /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint (w2n w) n a len) /\
  (!a len. a+len <= w2n w \/ w2n w+n <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n w) n a len) /\
  eval_operand buf.buf_operand t = SOME w /\ sa.cs_next_id < sb.cs_next_id ==>
  vv_post ctx func cenv cx e es sa sb s es (Value v)
    (LocatedValue (expr_type e) (base_ptr buf))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule literal_ptr_state_memory_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`p`, `sa`, `sh`] >> simp[] >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
     simp[] >> disch_then irule >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by metis_tac[] >>
  `!name a len. local_region cenv es.scopes t name a len <=>
    local_region cenv es.scopes u name a len` by
    (irule literal_ptr_local_region_frame >> simp[] >> metis_tac[]) >>
  `!name a len. local_region cenv es.scopes s name a len <=>
    local_region cenv es.scopes u name a len` by
    (irule literal_ptr_local_region_frame >> simp[] >> metis_tac[]) >>
  irule literal_ptr_memory_vv_post >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
      simp[] >> disch_then irule >>
      qpat_x_assum `!name a len. local_region _ _ u name a len ==> _` drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
      simp[] >> disch_then irule >>
      qpat_x_assum `!aid a len. _ ==> regions_disjoint _ _ a len` drule_all >>
      simp[regions_disjoint_def] >> decide_tac) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem literal_ptr_value_posts:
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w+val_footprint tv v ==> i NOTIN tn.t_mem) /\
  lookup_var p t = SOME w /\ FLOOKUP G p = SOME (b,n) /\
  b <= w2n w /\ w2n w+val_store_size tv v <= b+n /\
  w2n w+type_memory_bytes cenv (lowered_value_type cenv e) <= b+n /\
  op_taint tn (Var p) = {} /\ buf.buf_operand = Var p /\
  ~is_word_type (expr_type e) ==>
  ptr_vv_ok cx (expr_type e) (Value v)
    (LocatedValue (expr_type e) (base_ptr buf)) es G tn (t with vs_inst_idx := idx) /\
  ptr_val_ok cx (expr_type e) v (Var p) G tn (t with vs_inst_idx := idx) /\
  ptr_buf_ok cenv e (Var p) G (t with vs_inst_idx := idx)
Proof
  strip_tac >>
  `ptr_mem_ok cx (expr_type e) v (Var p) G tn (t with vs_inst_idx := idx)` by
    (irule literal_clean_ptr_mem_ok >>
     qexistsl_tac [`b`, `n`, `w`] >> gvs[lookup_var_def]) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, base_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  irule literal_site_ptr_buf_ok >>
  qexistsl_tac [`b`, `n`, `w`] >> gvs[lookup_var_def]
QED

Theorem literal_ptr_ghost_inv_normalize:
  ghost_inv d cenv cx (es with gas_obs := gs) G tn (s with vs_inst_idx := idx) <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def, stor_taint_ok_def,
       lookup_var_def] >> Cases_on `d` >> simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem literal_ptr_ghost_kept_initial_gas:
  ghost_kept cenv (es with gas_obs := gs) sa G tn s G' tn' <=>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[ghost_kept_def]
QED

Theorem literal_ptr_nonmemory_step[local]:
  (i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/ i.inst_opcode = MSTORE) /\
  step_inst_base i s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  asm_simp_tac bool_ss [] >>
  FIRST_PROVE [
    simp[exec_alloca_def, exec_pure2_def, exec_write2_def, AllCaseEqs(),
         update_var_def, mstore_def] >>
    rpt strip_tac >> gvs[]]
QED

Theorem literal_ptr_nonmemory_seq[local]:
  !code s t.
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/ i.inst_opcode = MSTORE) code /\
    run_inst_seq code s = OK t ==>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  rename1 `run_inst_seq code _ = _` >>
  `~is_terminator h.inst_opcode` by gvs[is_terminator_def] >>
  gvs[AllCaseEqs()] >>
  drule_at Any literal_ptr_nonmemory_step >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem literal_ptr_chunks_nonmemory_shape[local]:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/ i.inst_opcode = MSTORE)
      (emitted_insts sa sb)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  drule_all literal_chunk_head_shape >> strip_tac >>
  drule literal_payload_chunks_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[mk_inst_def]
QED

Theorem literal_bytelike_ptr_nonmemory_frame:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >> drule literal_ptr_bytelike_shape >> strip_tac >>
  drule literal_ptr_chunks_nonmemory_shape >> strip_tac >>
  irule literal_ptr_nonmemory_seq >> qexists_tac `emitted_insts sa sb` >>
  simp[mk_inst_def]
QED

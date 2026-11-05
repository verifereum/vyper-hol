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

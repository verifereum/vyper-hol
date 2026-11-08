(* Annotation-capacity literal construction: reuse the general chunk proofs. *)
Theory reasonLiteralBufferPtr
Ancestors exprSimPtrLiteralBuffer exprSimPtrLiteralPayload exprSimLiteralBuffer
  exprLowering exprLoweringProps context emitHelper compileEnv freshWrites
  vfmConstants venomInst list pair exprSimPtrLiteralChunks exprSimPtrLiteralOps
  fragExecPtr fragGasSeqPtr venomExecSemantics venomState ptrDiscipline words
  finite_map pred_set allocationPtr instIdxIndep fragExec bodyPtrDefs exprSimHash

Theorem reason_literal_compiler_parts:
  compile_bytelike_literal bs ml sa = (buf,sb) ==>
  ?sm sh.
    compile_alloc_buffer (32+32*word_size ml) sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
    compile_store_byte_chunks buf.buf_operand bs 32 sh = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     GSYM word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >> metis_tac[pairTheory.PAIR_EQ, pairTheory.pair_CASES]
QED

Theorem reason_literal_compiler_shape:
  compile_bytelike_literal bs ml sa = (buf,sb) ==>
  ?sm sh p.
    compile_alloc_buffer (32+32*word_size ml) sa = (buf,sm) /\
    emit_void MSTORE [Var p; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
    compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
    buf.buf_operand = Var p /\ p = STRING #"%" (toString sa.cs_next_var) /\
    ~not_fresh_at sa p /\ not_fresh_at sm p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    emitted_insts sa sm =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size ml))] [p]] /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size ml))] [p];
       mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] []] ++
      emitted_insts sh sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  drule reason_literal_compiler_parts >> strip_tac >>
  drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
  `ci_mono sh sb` by
    metis_tac[ci_mono_compile_store_byte_chunks, pairTheory.SND] >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    (irule emitted_insts_append >> simp[]) >>
  drule literal_payload_chunks_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  qexistsl_tac [`sm`, `sh`, `p`] >> simp[] >>
  gvs[ci_mono_def] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  decide_tac
QED

(* Full allocation capacity can exceed the initialized payload. *)
Theorem reason_literal_header_chunks_ptr:
  compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
  not_fresh_at sh p /\ lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,n) /\ 32+32*word_size (LENGTH bs) <= n /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  b+n < dimword (:256) ==>
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
  strip_tac >> `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn p s 32` by
    (simp[ptr_covers_def, w2n_n2w] >> decide_tac) >>
  `step_inst_base (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] []) s =
     OK (mstore b (n2w (LENGTH bs)) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
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
    (irule (cj 6 literal_chunks_ptr) >> simp[] >>
     qexistsl_tac [`b`, `n`, `p`] >> simp[] >> decide_tac) >>
  `b+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sb)` by
    (drule_at (Pat `compile_store_byte_chunks _ _ _ _ = _`)
       (REWRITE_RULE [GSYM AND_IMP_INTRO] (cj 5 literal_chunks_ptr)) >>
     rpt (disch_then drule) >> simp[] >>
     disch_then (mp_tac o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
     rpt (disch_then drule) >> simp[]) >>
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

Theorem reason_literal_buffer_ptr_run:
  compile_bytelike_literal bs ml sa = (buf,sb) /\ LENGTH bs <= ml /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+32*word_size ml < dimword (:256) ==>
  ?u t b p sh G' tn' dirty.
    buf.buf_operand = Var p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    stmt_state_rel ctx func cenv cx es u /\ u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size ml) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b (32+32*word_size ml) a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b (32+32*word_size ml) a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_labels = s.vs_labels /\ wb_frame cenv es sa s u /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
    (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    FLOOKUP G' p = SOME (b,32+32*word_size ml) /\
    lookup_var p t = SOME (n2w b) /\ op_taint tn' (Var p) = {} /\
    b+32+32*word_size ml < dimword (:256) /\
    mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    tn'.t_mem = (tn.t_mem UNION dirty) DIFF
      {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    dirty SUBSET {i | b <= i /\ i < b+32+32*word_size ml} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule reason_literal_compiler_shape >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size ml))] [p]) (fn_insts func)` by
    (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
  `word_size (LENGTH bs) <= word_size ml` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size ml))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by metis_tac[] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (32+32*word_size ml))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  suspend "payload"
QED

Resume reason_literal_buffer_ptr_run[payload]:
  qpat_x_assum `p = STRING _ _` kall_tac >>
  `w2n w = b` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `FLOOKUP u.vs_allocas _ = SOME (w2n w,_)` kall_tac >>
  qabbrev_tac `Ga = G |+ (p,(b,32+32*word_size ml))` >>
  qabbrev_tac `ta = tn with <|t_var := tn.t_var |+ (p,{}); t_mem := tn.t_mem UNION dirty|>` >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var p uh = SOME (n2w b) /\
   FLOOKUP Ga p = SOME (b,32+32*word_size ml) /\
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
    (irule reason_literal_header_chunks_ptr >> simp[] >>
     qexists_tac `32+32*word_size ml` >> simp[] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb)` by
    (qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >> simp[EVERY_MEM] >>
     metis_tac[]) >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`u`, `SUC s.vs_inst_idx`] assume_tac) >>
  Cases_on `run_inst_seq
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) u` >>
  fs[Abbr `uh`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `run_inst_seq _ (u with vs_inst_idx := _) = _` kall_tac >>
  qpat_x_assum `lookup_var p (u with vs_inst_idx := _) = _` kall_tac >>
  `b+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  suspend "assemble"
QED

Resume reason_literal_buffer_ptr_run[assemble]:
  qexistsl_tac [`u`, `v`, `b`, `sh`, `G'`, `tn'`, `dirty`] >>
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
  rpt strip_tac >> `x <> p` by metis_tac[] >> simp[FLOOKUP_UPDATE]
QED

Finalise reason_literal_buffer_ptr_run

Theorem reason_literal_buffer_ptr_path:
  compile_bytelike_literal bs ml sa = (buf,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all literal_bytelike_gas_path >> strip_tac >>
  simp[] >> drule reason_literal_compiler_shape >> strip_tac >>
  gvs[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.same_blocks_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.DROP_APPEND1] >>
  drule_at (Pat `isPREFIX _ _`)
    (REWRITE_RULE [GSYM AND_IMP_INTRO] run_inst_seq_gas_path_ptr) >>
  simp[mk_inst_def] >>
  disch_then (mp_tac o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  fs[mk_inst_def] >> rpt (disch_then drule) >> simp[arithmeticTheory.ADD1]
QED

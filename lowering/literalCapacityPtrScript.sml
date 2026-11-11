(* Literal construction at a declared capacity.  Unwritten capacity padding
   is not claimed to be zero or untainted. *)
Theory literalCapacityPtr
Ancestors
  exprSimPtrLiteralBuffer exprSimPtrLiteralOps exprSimPtrLiteralChunks
  exprSimLiteralBuffer exprSimPtrLiteralPayload allocationPtr bodyPtrDefs fragGasSeqPtr
  ptrDiscipline exprLowering context emitHelper emitHelperProps exprLoweringProps
  venomState venomInst venomExecSemantics instIdxIndep
  words arithmetic finite_map list rich_list pred_set vfmConstants fragExec freshWrites compileEnv
  exprSimHash valueEncoding

Theorem literal_capacity_header_chunks_ptr:
  compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
  not_fresh_at sh p /\ lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,cap) /\ 32+32*word_size (LENGTH bs) <= cap /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  b+cap < dimword(:256) ==>
  ?t Gf tnf.
    run_inst_seq (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb) s Gf tnf /\
    tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sh v ==> FLOOKUP Gf v = FLOOKUP G v /\
       FLOOKUP tnf.t_var v = FLOOKUP tn.t_var v)
Proof
  strip_tac >> `b < dimword(:256)` by decide_tac >>
  `ptr_covers G tn p s 32` by
    (simp[ptr_covers_def, w2n_n2w] >> decide_tac) >>
  `step_inst_base (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] []) s =
     OK (mstore b (n2w (LENGTH bs)) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
  drule literal_mstore_ghost >>
  disch_then (qspecl_then [`n2w (LENGTH bs)`,`tn`,`id`,`PG`,`G`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `th = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `lookup_var p uh = SOME (n2w b) /\ op_taint th (Var p) = {}` by
    (simp[Abbr `uh`, Abbr `u`, Abbr `th`, mstore_def, lookup_var_def, op_taint_def] >>
     fs[lookup_var_def, op_taint_def]) >>
  `?t Gf tnf. run_inst_seq (emitted_insts sh sb) uh = OK t /\
    inst_seq_ptr D 0 ctx fn PG G th (emitted_insts sh sb) uh Gf tnf /\
    tnf.t_mem = th.t_mem DIFF {i | b+32 <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tnf.t_stor = th.t_stor /\ tnf.t_trans = th.t_trans /\ tnf.t_imm = th.t_imm /\
    (!v. not_fresh_at sh v ==> lookup_var v t = lookup_var v uh /\
      FLOOKUP Gf v = FLOOKUP G v /\ FLOOKUP tnf.t_var v = FLOOKUP th.t_var v)` by
    (irule (cj 6 literal_chunks_ptr) >> simp[] >>
     qexistsl [`b`,`cap`,`p`] >> simp[] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sb)` by
    (irule (cj 5 literal_chunks_ptr) >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> qexistsl [`bs`,`32`] >> simp[] >> decide_tac) >>
  Cases_on `run_inst_seq (emitted_insts sh sb) u` >>
  fs[Abbr `uh`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qexistsl [`v`,`Gf`,`tnf`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, literal_mstore_ptr_inst_ok] >>
  gvs[Abbr `u`, Abbr `th`, w2n_n2w, mk_inst_def, LESS_MOD, is_terminator_def] >>
  rpt conj_tac >> simp[] >> simp[EXTENSION] >> rpt gen_tac >>
  eq_tac >> simp[] >> decide_tac
QED

Theorem literal_capacity_bytelike_shape:
  compile_bytelike_literal bs mx sa = (buf,sb) ==>
  ?sm sh p.
    compile_alloc_buffer (32+32*word_size mx) sa = (buf,sm) /\
    emit_void MSTORE [Var p; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
    compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
    buf.buf_operand = Var p /\ p = STRING #"%" (toString sa.cs_next_var) /\
    ~not_fresh_at sa p /\ not_fresh_at sm p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    emitted_insts sa sm =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size mx))] [p]] /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size mx))] [p];
       mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] []] ++
      emitted_insts sh sb /\
    sa.cs_next_id < sm.cs_next_id
Proof
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
  gvs[] >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists `sa` >> simp[]
QED

Theorem literal_capacity_bytelike_alloca_mem:
  compile_bytelike_literal bs mx sa = (buf,sb) /\ fn_has_code sa sb fn ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size mx))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)
Proof
  strip_tac >> drule literal_capacity_bytelike_shape >> strip_tac >>
  irule exprSimHashTheory.hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]
QED

Theorem literal_capacity_bytelike_ptr_run:
  compile_bytelike_literal bs mx sa = (buf,sb) /\ LENGTH bs <= mx /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+32*word_size mx < dimword(:256) ==>
  ?u t b p sh Gf tnf dirty.
    buf.buf_operand = Var p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size mx) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b (32+32*word_size mx) a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b (32+32*word_size mx) a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_labels = s.vs_labels /\ wb_frame cenv es es sa s u /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
    (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    FLOOKUP Gf p = SOME (b,32+32*word_size mx) /\
    lookup_var p t = SOME (n2w b) /\ op_taint tnf (Var p) = {} /\
    b+32+32*word_size mx < dimword(:256) /\
    mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    dirty SUBSET {i | b <= i /\ i < b+32+32*word_size mx} /\
    tnf.t_mem = (tn.t_mem UNION dirty) DIFF
      {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      FLOOKUP tnf.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule literal_capacity_bytelike_shape >> strip_tac >>
  drule_all literal_capacity_bytelike_alloca_mem >> strip_tac >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32+32*word_size mx))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size mx))] [p])
     (fn_insts fn)` by metis_tac[] >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  suspend "payload"
QED

Resume literal_capacity_bytelike_ptr_run[payload]:
  qpat_x_assum `p = STRING _ _` kall_tac >>
  `w2n w = b` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `FLOOKUP u.vs_allocas _ = SOME (w2n w,_)` kall_tac >>
  `word_size (LENGTH bs) <= word_size mx` by
    (simp[word_size_def] >> irule DIV_LE_MONOTONE >> decide_tac) >>
  qabbrev_tac `Ga = G |+ (p,(b,32+32*word_size mx))` >>
  qabbrev_tac `ta = tn with <|t_var := tn.t_var |+ (p,{}); t_mem := tn.t_mem UNION dirty|>` >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var p uh = SOME (n2w b) /\
   FLOOKUP Ga p = SOME (b,32+32*word_size mx) /\ op_taint ta (Var p) = {}` by
    (simp[Abbr `uh`, Abbr `Ga`, Abbr `ta`, lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     metis_tac[lookup_var_def]) >>
  `b+(32+32*word_size mx) < dimword(:256) /\
   32+32*word_size (LENGTH bs) <= 32+32*word_size mx /\
   b+32+32*word_size (LENGTH bs) < dimword(:256)` by decide_tac >>
  drule_all literal_capacity_header_chunks_ptr >>
  disch_then (qspecl_then [`sm.cs_next_id`,`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb)` by
    (drule literal_bytelike_counted_shape >> strip_tac >> fs[EVERY_MEM]) >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`u`,`SUC s.vs_inst_idx`] assume_tac) >>
  Cases_on `run_inst_seq
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) u` >>
  fs[Abbr `uh`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `run_inst_seq _ (u with vs_inst_idx := _) = _` kall_tac >>
  qpat_x_assum `lookup_var p (u with vs_inst_idx := _) = _` kall_tac >>
  `b+32+32*word_size (LENGTH bs) < dimword(:256)` by decide_tac >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  suspend "assemble"
QED

Resume literal_capacity_bytelike_ptr_run[assemble]:
  qexistsl [`u`,`v`,`b`,`sh`,`Gf`,`tnf`,`dirty`] >> simp[] >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[run_inst_seq_def] >>
      asm_simp_tac bool_ss [] >> simp[mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[inst_seq_ptr_def] >>
      asm_simp_tac bool_ss [] >> simp[literal_alloca_ptr_inst_ok]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- (qpat_x_assum `v with <|vs_vars := _; vs_memory := _|> = u` mp_tac >> simp[]) >>
  conj_tac >- metis_tac[ADD_ASSOC, ADD_COMM] >>
  conj_tac
  >- (qpat_x_assum `!v. not_fresh_at sh v ==> _` (qspec_then `p` mp_tac) >>
      simp[op_taint_def, Abbr `ta`, FLOOKUP_UPDATE]) >>
  simp[Abbr `ta`, Abbr `Ga`] >>
  rpt strip_tac >> `x <> p` by metis_tac[] >> simp[FLOOKUP_UPDATE]
QED

Finalise literal_capacity_bytelike_ptr_run

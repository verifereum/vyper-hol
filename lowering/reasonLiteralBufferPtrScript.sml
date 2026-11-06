(* Annotation-capacity literal construction: reuse the general chunk proofs. *)
Theory reasonLiteralBufferPtr
Ancestors exprSimPtrLiteralBuffer exprSimPtrLiteralPayload exprSimLiteralBuffer
  exprLowering exprLoweringProps context emitHelper compileEnv freshWrites
  vfmConstants venomInst list pair exprSimPtrLiteralChunks exprSimPtrLiteralOps
  fragExecPtr fragGasSeqPtr venomExecSemantics venomState ptrDiscipline words
  finite_map pred_set allocationPtr instIdxIndep fragExec bodyPtrDefs

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

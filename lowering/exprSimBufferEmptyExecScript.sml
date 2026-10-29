(*
 * Execution of empty(T) buffers (#636)
 *
 * compile_builtin_empty_complex allocates a buffer and zeroes it a word at
 * a time (compile_zero_words).  The code runs and keeps stmt_state_rel,
 * the buffer is disjoint from older allocations and the locals, and the
 * result has a zero header word or sz zero bytes.  Allocation itself need
 * not clear memory.
 *
 * TOP-LEVEL:
 *   compile_builtin_empty_complex_run, compile_builtin_empty_complex_frag —
 *     the run of the emitted code, and the same as a frag_exec
 *   compile_builtin_empty_complex_shape — the code is straight-line
 *   compile_zero_words_run — compile_zero_words zeroes 32 * n bytes and
 *     nothing else
 *
 * Helpers: the buffer_zero_words_*, empty_tail_* and
 *   empty_compile_decompose lemmas.
 *)
Theory exprSimBufferEmptyExec
Ancestors
  exprSimBuffer exprSimBufferEmpty builtinSimple exprSimBufferStore
  exprSimLiteralBuffer exprSimOps freshWrites valueEncodingProps
  exprSimWordArgs emitHelperProps exprLoweringProps compileEnv context
  venomInst venomState words fragExec rich_list list

Theorem buffer_zero_words_shape[local]:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + n /\
    sb.cs_next_id = sa.cs_next_id + 2*n
Proof
  Induct_on `n`
  >- simp[compile_zero_words_def, comp_return_def, same_blocks_def,
          emitted_insts_def] >>
  rpt gen_tac >>
  simp[Once compile_zero_words_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> rename1 `compile_zero_words pop n sa = (u,sm)` >>
  Cases_on `u` >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  gvs[same_blocks_def, emitted_insts_def, DROP_APPEND1]
QED

Theorem buffer_zero_words_run_frame[local]:
  !n pop sa sb s w sz.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!p. pop = Var p ==> not_fresh_at sa p) /\
    32*n <= sz /\ w2n w + sz < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand pop t = SOME w /\
      mem_bytes_at (w2n w) (32*n) t.vs_memory = REPLICATE (32*n) 0w /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!a len. a+len <= w2n w \/ w2n w+32*n <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  Induct_on `n`
  >- (simp[compile_zero_words_def, comp_return_def] >> rpt strip_tac >>
      qexists_tac `s` >> simp[emitted_insts_refl, run_inst_seq_def,
                              valueEncodingTheory.mem_bytes_at_def]) >>
  rpt gen_tac >>
  simp[Once compile_zero_words_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> rename1 `compile_zero_words pop n sa = (u,sm)` >>
  Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD _ sm = (dst,sadd)` >>
  `32*n <= sz /\ 32*n+32 <= sz` by decide_tac >>
  qpat_x_assum `!pop sa sb s w sz. _`
    (qspecl_then [`pop`,`sa`,`sm`,`s`,`w`,`sz`] mp_tac) >>
  simp[] >> strip_tac >>
  drule buffer_zero_words_shape >> strip_tac >>
  drule_all buffer_emit_add_run >> strip_tac >>
  qabbrev_tac `v = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `ta = update_var v (w + n2w (32*n)) t` >>
  `eval_operand dst ta = SOME (w + n2w (32*n))` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[Abbr `ta`, Abbr `v`, eval_operand_def, lookup_var_update_var]) >>
  `w2n (w + n2w (32*n)) = w2n w + 32*n` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> simp[]) >>
  `run_inst_seq (emitted_insts sadd sb) ta =
     OK (mstore (w2n w+32*n) 0w ta)` by
    (drule literal_emit_mstore_run >>
     disch_then (qspecl_then [`ta`,`w+n2w (32*n)`,`0w`] mp_tac) >>
     simp[eval_operand_def]) >>
  drule emit_op_extends >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `sadd.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sadd /\
   sb.cs_current_insts = sadd.cs_current_insts ++ emitted_insts sadd sb` by
    metis_tac[emitted_insts_emit_op, emitted_insts_emit_void] >>
  `run_inst_seq (emitted_insts sa sadd) s = OK ta /\
   sadd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sadd` by
    (qspecl_then [`sa`,`sm`,`sadd`] mp_tac run_inst_seq_chain >>
     disch_then (qspecl_then [`s`,`t`] mp_tac) >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n w+32*n) 0w ta)` by
    (qspecl_then [`sa`,`sadd`,`sb`] mp_tac run_inst_seq_chain >>
     disch_then (qspecl_then [`s`,`ta`] mp_tac) >> simp[]) >>
  qexists_tac `mstore (w2n w+32*n) 0w ta` >>
  conj_tac >- first_assum ACCEPT_TAC >> suspend "frames"
QED

Resume buffer_zero_words_run_frame[frames]:
  `!x. not_fresh_at sa x ==> lookup_var x ta = lookup_var x s` by
    (rpt strip_tac >>
     `x <> v` by
       (gvs[not_fresh_at_def, Abbr `v`, ASCIInumbersTheory.toString_11] >>
        decide_tac) >>
     simp[Abbr `ta`, lookup_var_update_var]) >>
  conj_tac >- (Cases_on `pop` >>
    gvs[eval_operand_def, lookup_var_def, mstore_def, Abbr `ta`, update_var_def]) >>
  conj_tac
  >- (`32*SUC n = 32*n+32` by decide_tac >>
      `ta.vs_memory = t.vs_memory` by simp[Abbr `ta`, update_var_def] >>
      qpat_x_assum `32*SUC n = _` (fn th => pure_rewrite_tac[th]) >>
      irule mem_bytes_at_zero_extend >> simp[]) >>
  simp[] >> conj_tac
  >- (simp[Abbr `ta`, update_var_def, mstore_def,
           write_memory_with_expansion_def]) >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at a len (mstore (32*n+w2n w) 0w ta).vs_memory =
   mem_bytes_at a len ta.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `a+len <= w2n w \/ 32*n+w2n w <= a` by decide_tac >>
  simp[Abbr `ta`, update_var_def]
QED

Finalise buffer_zero_words_run_frame

Theorem compile_zero_words_run:
  !n pop sa sb s w sz func cenv cx es.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!p. pop = Var p ==> not_fresh_at sa p) /\
    stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    32*n <= sz /\ w2n w+sz < dimword (:256) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
       w2n w+sz <= b \/ b+len <= w2n w) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel func cenv cx es t /\ eval_operand pop t = SOME w /\
      mem_bytes_at (w2n w) (32*n) t.vs_memory = REPLICATE (32*n) 0w /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!a len. a+len <= w2n w \/ w2n w+32*n <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all buffer_zero_words_run_frame >> strip_tac >>
  qexists_tac `t` >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  irule literal_state_memory_frame >> qexists_tac `s` >> simp[] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by
        (gvs[local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `w2n w+sz <= b \/ b+sz' <= w2n w` by metis_tac[] >>
  `b+sz' <= w2n w \/ w2n w+32*n <= b` by decide_tac >>
  simp[]
QED

Theorem empty_word_count[local]:
  !sz. sz MOD 32 = 0 ==> 32*((sz+31) DIV 32) = sz
Proof
  rpt strip_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `sz` mp_tac) >> simp[] >> strip_tac >>
  `sz+31 = 32*(sz DIV 32)+31` suffices_by
    (disch_then SUBST1_TAC >> simp[]) >> decide_tac
QED

Theorem empty_tail_run[local]:
  !header pop sz sa sb s w func cenv cx es.
    (if header then emit_void MSTORE [pop; Lit 0w]
     else compile_zero_words pop ((sz+31) DIV 32)) sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!p. pop = Var p ==> not_fresh_at sa p) /\
    stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    w2n w+sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      w2n w+sz <= b \/ b+len <= w2n w) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel func cenv cx es t /\ eval_operand pop t = SOME w /\
      mem_bytes_at (w2n w) (if header then 32 else sz) t.vs_memory =
        REPLICATE (if header then 32 else sz) 0w /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!a len. a+len <= w2n w \/ w2n w+sz <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  Cases_on `header` >> simp[] >> rpt gen_tac >> strip_tac
  >- suspend "header"
  >> drule empty_word_count >> strip_tac >>
  drule compile_zero_words_run >>
  disch_then (qspecl_then [`s`,`w`,`sz`,`func`,`cenv`,`cx`,`es`] mp_tac) >>
  simp[] >> (impl_tac >- (rpt strip_tac >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Resume empty_tail_run[header]:
  `run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n w) 0w s)` by
    (drule literal_emit_mstore_run >>
     disch_then (qspecl_then [`s`,`w`,`0w`] mp_tac) >> simp[eval_operand_def]) >>
  qexists_tac `mstore (w2n w) 0w s` >> simp[] >>
  conj_tac
  >- (irule literal_mstore_state_rel >> simp[] >>
      qexistsl_tac [`w2n w`,`sz`] >> simp[] >> metis_tac[]) >>
  `mem_bytes_at (w2n w) 0 s.vs_memory = REPLICATE 0 0w` by
    simp[valueEncodingTheory.mem_bytes_at_def] >>
  drule mem_bytes_at_zero_extend >> simp[] >> strip_tac >>
  conj_tac >- (Cases_on `pop` >> gvs[eval_operand_def, mstore_def]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Finalise empty_tail_run

Theorem empty_tail_shape[local]:
  !header pop sz sa sb.
    (if header then emit_void MSTORE [pop; Lit 0w]
     else compile_zero_words pop ((sz+31) DIV 32)) sa = ((),sb) ==>
    cs_extends sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  Cases_on `header` >> simp[] >> rpt gen_tac >> strip_tac
  >- (drule emit_void_extends >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      gvs[emitHelperTheory.emit_void_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def] >>
      irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule buffer_zero_words_shape >> strip_tac >> simp[] >>
  irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]
QED

Theorem empty_compile_decompose[local]:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    ?sm. compile_alloc_buffer sz sa = (buf,sm) /\
      (if header then emit_void MSTORE [buf.buf_operand; Lit 0w]
       else compile_zero_words buf.buf_operand ((sz+31) DIV 32)) sm = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_builtin_empty_complex_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> rename1 `compile_alloc_buffer sz sa = (ba,sm)` >>
  simp[] >> Cases_on `header` >> simp[comp_bind_def, comp_ignore_bind_def,
                                     comp_return_def] >>
  pairarg_tac >> rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >>
  strip_tac >> gvs[] >> qexists_tac `sm` >> simp[]
QED

Theorem compile_builtin_empty_complex_run:
  !sz header sa sb buf func cenv cx es s.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w+sz < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
      (if header then mem_word_at (w2n w) t.vs_memory = 0w
       else mem_bytes_at (w2n w) sz t.vs_memory = REPLICATE sz 0w) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) sz b len) /\
      (!a len. a+len <= w2n w \/ w2n w+sz <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> drule empty_compile_decompose >> strip_tac >>
  drule empty_tail_shape >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sa.cs_next_id < sm.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, DROP_APPEND1] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region cenv es.scopes t name b len ==>
    w2n w+sz <= b \/ b+len <= w2n w` by
    (gvs[regions_disjoint_def] >> metis_tac[]) >>
  drule empty_tail_run >>
  disch_then (qspecl_then [`t`,`w`,`func`,`cenv`,`cx`,`es`] mp_tac) >>
  simp[] >> (impl_tac >- (rpt strip_tac >>
    qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
    decide_tac)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK q` >>
  `run_inst_seq (emitted_insts sa sb) s = OK q` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  qexistsl_tac [`q`,`w`] >> simp[] >> suspend "package"
QED

Resume compile_builtin_empty_complex_run[package]:
  `q.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  simp[] >> conj_tac
  >- (Cases_on `header` >> gvs[] >>
      drule mem_word_at_zero_range >>
      disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

Finalise compile_builtin_empty_complex_run

Theorem buffer_zero_words_safe[local]:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  Induct_on `n`
  >- simp[compile_zero_words_def, comp_return_def, emitted_insts_refl] >>
  rpt gen_tac >>
  simp[Once compile_zero_words_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> rename1 `compile_zero_words pop n sa = (u,sm)` >>
  Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule buffer_zero_words_shape >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp_tac (srw_ss()) [Once emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, EVERY_APPEND,
                   EVERY_DEF, venomInstTheory.mk_inst_def] >>
  simp[venomInstTheory.is_terminator_def]
QED

Theorem compile_builtin_empty_complex_shape:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >> drule empty_compile_decompose >> strip_tac >>
  Cases_on `header` >> gvs[]
  >- (gvs[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      simp[emitted_insts_def, DROP_APPEND1, IS_PREFIX_APPEND,
           venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule buffer_zero_words_shape >> strip_tac >>
  drule buffer_zero_words_safe >> strip_tac >>
  gvs[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, same_blocks_def] >>
  conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, IS_PREFIX_APPEND] >>
      metis_tac[]) >>
  simp_tac (srw_ss()) [Once emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, EVERY_APPEND,
                   EVERY_DEF, venomInstTheory.mk_inst_def] >>
  gvs[venomInstTheory.is_terminator_def, venomInstTheory.mk_inst_def]
QED

Theorem compile_builtin_empty_complex_frag:
  !sz header sa sb buf ctx P Q R.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    frag_exec ctx sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> metis_tac[]
QED

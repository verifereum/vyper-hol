(*
 * Stores into expression buffers (#636)
 *
 * The lowering writes a child's value into its parent's buffer with
 * compile_store_memory: a word store, an MCOPY, or a bytestring store.
 * The code runs, val_in_memory holds at the destination, and only the
 * destination window changes; stmt_state_rel survives when that window is
 * clear of the locals.
 *
 * TOP-LEVEL:
 *   buffer_store_memory_shape — compile_store_memory only appends
 *     instructions
 *   buffer_store_memory_encoding — it runs and leaves the value at the
 *     destination, and other variables and memory alone
 *   buffer_store_state_frame — such a change keeps stmt_state_rel
 *
 * Helpers: buffer_round_*, the MCOPY and bytestring runs
 *   (buffer_copy_*, buffer_mcopy_*, buffer_store_bytestring_* lemmas),
 *   buffer_window_byte.
 *)
Theory exprSimBufferStore
Ancestors
  exprSimBuffer exprSimLiteralBuffer words integer_word vfmConstants emitHelperProps
  exprLoweringProps context venomExecSemantics venomState compileEnv
  copyFwdEquiv allocaRemapDefs valueEncodingProofs list rich_list
  exprSimMemoryTransport valueEncodingProps entryDecodeProps entryDecodeStaticProps

Theorem buffer_round_mask:
  !w:bytes32. w && i2w (- &32) = (w >>> 5) << 5
Proof
  `i2w (- &32):bytes32 = (-1w:bytes32) << 5` by
    (EVAL_TAC >> CONV_TAC wordsLib.WORD_EVAL_CONV) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp_tac (bool_ss ++ fcpLib.FCP_ss)
    [word_and_def, word_lsl_def, word_lsr_def, WORD_NEG_1, word_T] >>
  rpt strip_tac >> Cases_on `5 <= i` >>
  asm_simp_tac (arith_ss ++ fcpLib.FCP_ss) [WORD_NEG_1, word_T]
QED

Theorem buffer_round_no_wrap:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    len + 31 < dimword (:256)
Proof
  rpt gen_tac >> rewrite_tac[word_size_def] >> strip_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `len + 31` strip_assume_tac) >>
  `(len + 31) MOD 32 < 32` by simp[] >>
  gvs[] >> intLib.ARITH_TAC
QED

Theorem buffer_round_size:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    ((((n2w len:bytes32) + 31w) && i2w (- &32)) + 32w =
     n2w (32 + 32 * word_size len))
Proof
  rpt strip_tac >> drule buffer_round_no_wrap >> strip_tac >>
  rewrite_tac[buffer_round_mask, word_add_n2w] >>
  `n2w (len + 31):bytes32 >>> 5 = n2w ((len + 31) DIV 32)` by
    (simp[GSYM n2w_DIV]) >>
  simp[word_size_def, word_lsl_n2w, word_add_n2w] >>
  AP_TERM_TAC >> decide_tac
QED

Theorem buffer_emit_mcopy_run:
  !sa sb dst src sz d w n s.
    emit_void MCOPY [dst; src; sz] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    eval_operand sz s = SOME n ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (mcopy (w2n d) (w2n w) (w2n n) s)
Proof
  rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [dst; src; sz] []) s =
     OK (mcopy (w2n d) (w2n w) (w2n n) s)` by
    simp[step_inst_base_def] >>
  simp[run_inst_seq_def]
QED

Theorem buffer_copy_memory_run:
  !dst src n sa sb s d w.
    compile_copy_memory dst src n sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    n < dimword (:256) ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (if n = 0 then s else mcopy (w2n d) (w2n w) n s)
Proof
  rpt strip_tac >> Cases_on `n = 0`
  >- gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def,
         run_inst_seq_def] >>
  Cases_on `n` >> gvs[compile_copy_memory_def] >>
  drule buffer_emit_mcopy_run >>
  disch_then drule >> disch_then drule >>
  simp[eval_operand_def]
QED

Theorem buffer_copy_memory_shape:
  !dst src n sa sb.
    compile_copy_memory dst src n sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var /\
    sb.cs_next_id = sa.cs_next_id + (if n = 0 then 0 else 1)
Proof
  rpt strip_tac >> Cases_on `n` >>
  gvs[compile_copy_memory_def, comp_return_def,
      emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
      emit_def, comp_ignore_bind_def, same_blocks_def, emitted_insts_def,
      rich_listTheory.DROP_APPEND1]
QED

Theorem buffer_copy_len_shape:
  !src out sa sb.
    compile_bytestring_copy_len src sa = (out,sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 4
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED


Theorem buffer_copy_len_run:
  !src out sa sb s w len.
    compile_bytestring_copy_len src sa = (out,sb) /\
    eval_operand src s = SOME w /\ mload (w2n w) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      eval_operand out q = SOME (n2w (32 + 32 * word_size len)) /\
      (q with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  drule_then assume_tac step_MLOAD >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst aid ADD ops [v1]) s1` >>
  `step_inst_base (mk_inst aid ADD ops [v1]) s1 =
     OK (update_var v1 ((n2w len:bytes32) + 31w) s1)` by
    (simp[Abbr `ops`] >> irule step_ADD >> simp[Abbr `s1`, eval_operand_def,
                           lookup_var_update_var]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst bid AND bops [v2]) s2` >>
  `step_inst_base (mk_inst bid AND bops [v2]) s2 =
     OK (update_var v2 (((n2w len:bytes32) + 31w) && i2w (- &32)) s2)` by
    (qunabbrev_tac `bops` >> irule step_AND >> simp[Abbr `s2`, eval_operand_def,
                           lookup_var_update_var]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst cid ADD cops [v3]) s3` >>
  `step_inst_base (mk_inst cid ADD cops [v3]) s3 =
     OK (update_var v3 ((((n2w len:bytes32) + 31w) && i2w (- &32)) + 32w) s3)` by
    (simp[Abbr `cops`] >> irule step_ADD >> simp[Abbr `s3`, eval_operand_def,
                           lookup_var_update_var]) >>
  simp[] >>
  conj_tac
  >- (qspec_then `len` mp_tac buffer_round_size >>
      simp[eval_operand_def, lookup_var_update_var]) >>
  simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def] >>
  rpt strip_tac >>
  gvs[not_fresh_at_def, Abbr `v1`, Abbr `v2`, Abbr `v3`,
      ASCIInumbersTheory.toString_11, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem buffer_store_bytestring_shape:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 5
Proof
  rpt strip_tac >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem buffer_store_bytestring_run:
  !src dst sa sb s w d len.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      q.vs_memory = (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) s).vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_store_bytestring_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_bytestring_copy_len src sa = (out,mid)` >>
  drule_all buffer_copy_len_run >> strip_tac >>
  drule buffer_copy_len_shape >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  `q.vs_memory = s.vs_memory` by
    (qpat_x_assum `q with vs_vars := _ = s`
       (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  `q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` by
    (qpat_assum `q with vs_vars := _ = s`
       (mp_tac o AP_TERM ``\z. z with vs_memory := s.vs_memory``) >> simp[]) >>
  `eval_operand src q = SOME w` by
    (`eval_operand src q = eval_operand src s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  `eval_operand dst q = SOME d` by
    (`eval_operand dst q = eval_operand dst s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  drule_all buffer_emit_mcopy_run >> strip_tac >>
  qexists_tac `mcopy (w2n d) (w2n w) (32 + 32 * word_size len) q` >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq (emitted_insts sa mid) s = OK q`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> gvs[]) >>
  simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  fs[lookup_var_def]
QED

Theorem buffer_window_byte:
  !off len mem i. i < len ==>
    EL i (mem_bytes_at off len mem) = mem_byte_at mem (off + i)
Proof
  simp[EL_mem_bytes_at, mem_byte_at_def]
QED

Theorem buffer_mcopy_window:
  !dst src n s off k. off + k <= n ==>
    mem_bytes_at (dst + off) k (mcopy dst src n s).vs_memory =
    mem_bytes_at (src + off) k s.vs_memory
Proof
  rpt strip_tac >> irule LIST_EQ >>
  simp_tac bool_ss [LENGTH_mem_bytes_at_proof] >> rpt strip_tac >>
  asm_simp_tac bool_ss [buffer_window_byte] >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  irule (SRULE [LET_THM] mcopy_establishes_equiv) >> decide_tac
QED

Theorem buffer_mcopy_exterior:
  !dst src n s a k. a + k <= dst \/ dst + n <= a ==>
    mem_bytes_at a k (mcopy dst src n s).vs_memory =
    mem_bytes_at a k s.vs_memory
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[buffer_window_byte] >>
  irule (SRULE [LET_THM] mcopy_preserves_disjoint) >>
  qexists_tac `k` >> simp[]
QED

Theorem buffer_mcopy_restore:
  !dst src n s. (mcopy dst src n s with vs_memory := s.vs_memory) = s
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem buffer_mcopy_encoding:
  !tv v src dst n s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    val_in_memory tv v dst (mcopy dst src n s).vs_memory
Proof
  rpt strip_tac >> irule val_in_memory_relocate_footprint >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `src`] >> simp[] >>
  metis_tac[buffer_mcopy_window, arithmeticTheory.ADD_CLAUSES]
QED

Theorem buffer_bytes_header:
  !cap bs src s.
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) src s.vs_memory ==>
    mload src s = n2w (LENGTH bs)
Proof
  simp[valueEncodingTheory.val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem buffer_string_header:
  !cap str src s.
    val_in_memory (BaseTV (StringT cap)) (StringV str) src s.vs_memory ==>
    mload src s = n2w (LENGTH str)
Proof
  simp[valueEncodingTheory.val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem buffer_store_memory_shape:
  !cenv src dst ty sa sb.
    compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emit_void_extends >>
      simp[cs_extends_def] >> strip_tac >>
      drule emitted_insts_emit_void >> simp[]) >>
  Cases_on `is_bytestring_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule buffer_store_bytestring_shape >> simp[]) >>
  gvs[compile_store_memory_def] >> drule buffer_copy_memory_shape >> simp[]
QED

Theorem buffer_copy_memory_encoding:
  !dst src n sa sb s d w tv v.
    compile_copy_memory dst src n sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    n < dimword (:256) /\ val_in_memory tv v (w2n w) s.vs_memory /\
    val_wf tv v /\ val_footprint tv v <= n ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with vs_memory := s.vs_memory) = s /\
      (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> drule_all buffer_copy_memory_run >>
  strip_tac >> Cases_on `n = 0`
  >- (gvs[] >> irule val_in_memory_relocate_footprint >> simp[] >>
      qexistsl_tac [`s.vs_memory`, `w2n w`] >>
      simp[valueEncodingTheory.mem_bytes_at_def]) >>
  gvs[] >> conj_tac
  >- (irule buffer_mcopy_encoding >> simp[]) >>
  simp[buffer_mcopy_restore] >> rpt gen_tac >> strip_tac >>
  irule buffer_mcopy_exterior >> decide_tac
QED

Theorem buffer_store_word_encoding:
  !src dst sa sb s d w tenv ty tv v.
    emit_void MSTORE [dst;src] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ w = typed_val_to_w256 tv v ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with vs_memory := s.vs_memory) = s /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> drule_all literal_emit_mstore_run >>
  strip_tac >> simp[] >> conj_tac
  >- (drule_all val_in_memory_word >>
      disch_then (qspecl_then [`w2n d`, `(mstore (w2n d) w s).vs_memory`]
        mp_tac) >> simp[mstore_mem_word_at_same]) >>
  conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def] >>
  drule_all word_type_memory_size >> strip_tac >>
  rpt gen_tac >> strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  gvs[] >> decide_tac
QED

Theorem buffer_store_bytestring_encoding:
  !src dst sa sb s w d len tv v.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v = 32 + 32 * word_size len /\
    type_memory_size tv < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `32 + 32 * word_size len <= type_memory_size tv` by
    metis_tac[exprSimTheory.val_footprint_le] >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  drule_all buffer_store_bytestring_run >> strip_tac >>
  qexists_tac `q` >> simp[] >> conj_tac
  >- (irule buffer_mcopy_encoding >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule buffer_mcopy_exterior >> decide_tac
QED

Theorem buffer_typed_bytestring_header:
  !tenv ty tv v p s.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ val_in_memory tv v p s.vs_memory ==>
    ?len. mload p s = n2w len /\
      val_footprint tv v = 32 + 32 * word_size len
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >>
      gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
      drule buffer_bytes_header >> strip_tac >>
      qexists_tac `LENGTH l` >> simp[exprSimTheory.val_footprint_def]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  drule buffer_string_header >> strip_tac >>
  qexists_tac `LENGTH s'` >> simp[exprSimTheory.val_footprint_def]
QED

Theorem buffer_store_memory_encoding:
  !cenv cx src dst ty sa sb tv v s d.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ expr_val_rel cx ty v src s /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[exprSimTheory.expr_val_rel_def] >>
  Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule_all (SRULE [] buffer_store_word_encoding) >> strip_tac >>
      `q.vs_vars = s.vs_vars` by
        (qpat_assum `q with vs_memory := _ = s`
          (mp_tac o AP_TERM ``\z. z.vs_vars``) >> simp[]) >>
      `q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` by
        (qpat_assum `q with vs_memory := _ = s`
          (mp_tac o AP_TERM ``\z. z with vs_vars := s.vs_vars``) >> simp[]) >>
      qexists_tac `q` >> simp[lookup_var_def] >> conj_tac
      >- (Cases_on `q` >> Cases_on `s` >> gvs[]) >>
      rpt gen_tac >> strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[] >> Cases_on `is_bytestring_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      drule_all (SRULE [] buffer_store_bytestring_encoding) >>
      strip_tac >> qexists_tac `q` >> simp[] >>
      rpt gen_tac >> strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[compile_store_memory_def] >>
  `val_footprint tv v <= type_memory_size tv` by
    simp[exprSimTheory.val_footprint_le] >>
  drule_all (SRULE [] buffer_copy_memory_encoding) >> strip_tac >>
  `q.vs_vars = s.vs_vars` by
    (qpat_assum `q with vs_memory := _ = s`
      (mp_tac o AP_TERM ``\z. z.vs_vars``) >> simp[]) >>
  `q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` by
    (qpat_assum `q with vs_memory := _ = s`
      (mp_tac o AP_TERM ``\z. z with vs_vars := s.vs_vars``) >> simp[]) >>
  qexists_tac `q` >> simp[lookup_var_def] >> conj_tac
  >- (Cases_on `q` >> Cases_on `s` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem buffer_store_memory_capacity:
  !cenv cx src dst ty sa sb tv v s d q.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ expr_val_rel cx ty v src s /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    run_inst_seq (emitted_insts sa sb) s = OK q ==>
    LENGTH s.vs_memory <= LENGTH q.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  gvs[exprSimTheory.expr_val_rel_def] >>
  Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule_all literal_emit_mstore_run >> strip_tac >> gvs[] >>
      simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
           arithmeticTheory.MAX_DEF]) >>
  gvs[] >> Cases_on `is_bytestring_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      `32 + 32 * word_size len <= type_memory_size tv` by
        metis_tac[exprSimTheory.val_footprint_le] >>
      `32 + 32 * word_size len < dimword (:256)` by
        (simp[dimword_def] >> decide_tac) >>
      drule_all buffer_store_bytestring_run >> strip_tac >> gvs[] >>
      simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
           arithmeticTheory.MAX_DEF]) >>
  gvs[compile_store_memory_def] >>
  drule_all (SRULE [dimword_def] buffer_copy_memory_run) >> strip_tac >>
  Cases_on `type_memory_size tv = 0` >> gvs[] >>
  simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
       arithmeticTheory.MAX_DEF]
QED

Theorem buffer_store_state_frame:
  !func cenv cx es sa s q dst n ctx.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a+k <= dst \/ dst+n <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      b+sz <= dst \/ dst+n <= b) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module,name)) =
        SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) dst n) ==>
    stmt_state_rel ctx func cenv cx es q
Proof
  rpt gen_tac >> strip_tac >> irule literal_state_memory_frame >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at a k _ = _` irule >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
      gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k _ = _` irule >>
  gvs[regions_disjoint_def] >> metis_tac[]
QED

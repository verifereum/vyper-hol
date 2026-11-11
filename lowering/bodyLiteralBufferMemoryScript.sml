(* Counted memory simulation of a bytes or string literal that is not a word:
   the lowering writes it into a buffer of its own (compile_bytelike_literal,
   an ALLOCA, the length word and the bytes in 32-byte chunks).

   exprSimLiteralBuffer has the run (literal_bytelike_run) and its value
   post (literal_memory_vv_post).  What the memory judgments add:
   - every store lies in the buffer, which ends below the allocation
     frontier (alloca_next_valid), so the run is memory-safe;
   - the run only grows the frontier (one ALLOCA, then ADDs and MSTOREs)
     and keeps the allocation history;
   - the value's rounded footprint, val_store_size, is the buffer's size,
     which is the store bound. *)
Theory bodyLiteralBufferMemory
Ancestors
  exprSimLiteralBuffer exprSimMemDefs exprSimMemoryPath exprSimUnwrapProps
  fragGasSeqMem allocaHistoryFragment allocaFootprint instMemFrontier
  fragExecMem fragGasPathMem fragGasMode gasSummary gasOutcome
  exprSimVVFrame exprSimAlloc exprSimProps exprSimDefs exprSimHypsDefs
  loweringPosts allocLimits exprLoweringProps exprLowering emitHelperProps
  emitHelper context compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs vyperAST vyperInterpreter
  vyperState vyperValue vyperValueOperation vyperTypeSystem
  venomState venomInst venomExecSemantics venomMemDefs venomMemProps
  list rich_list finite_map words arithmetic

Theorem literal_chunk_span[local]:
  !n. 0 < n ==> 32 + 32 * word_size (n - 32) = 32 * word_size n
Proof
  rw[vfmConstantsTheory.word_size_def] >> Cases_on `n < 32`
  >- (`n - 32 = 0` by simp[] >>
      `(n + 31) DIV 32 = 1` by
        (irule DIV_UNIQUE >> qexists_tac `n - 1` >> simp[]) >>
      simp[]) >>
  `n + 31 = 1 * 32 + (n - 32 + 31)` by simp[] >>
  pop_assum SUBST1_TAC >> simp[ADD_DIV_ADD_DIV]
QED

Theorem literal_chunk_head_mem_ok[local]:
  eval_operand pop s = SOME x /\ w2n (x + n2w off) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok [mk_inst i ADD [pop; Lit (n2w off)] [p];
                       mk_inst j MSTORE [Var p; Lit wv] []] s
Proof
  strip_tac >>
  `step_inst_base (mk_inst i ADD [pop; Lit (n2w off)] [p]) s =
     OK (update_var p (x + n2w off) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  simp[eval_operand_def, lookup_var_update_var, update_var_def] >>
  simp[mk_inst_def, below_frontier_no_ranges]
QED

(* The chunk stores write inside [b + off, b + off + 32 * word_size n),
   below the frontier, and touch no allocation. *)
Theorem literal_chunks_mem:
  !ptr bs off sa sb s b.
    compile_store_byte_chunks ptr bs off sa = ((),sb) /\
    (!x. ptr = Var x ==> not_fresh_at sa x) /\
    eval_operand ptr s = SOME (n2w b) /\
    b + off + 32 * word_size (LENGTH bs) <= s.vs_alloca_next /\
    b + off + 32 * word_size (LENGTH bs) < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    !t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
        t.vs_alloca_next = s.vs_alloca_next
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_store_byte_chunks_def, comp_return_def,
          emitted_insts_def, run_inst_seq_mem_ok_def, run_inst_seq_def]) >>
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
  qmatch_asmsub_abbrev_tac `emit_void MSTORE [dst; Lit wv] mid` >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  `emitted_insts sa post =
     [mk_inst sa.cs_next_id ADD [data_ptr; Lit (n2w offset)] [p];
      mk_inst mid.cs_next_id MSTORE [Var p; Lit wv] []]` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `post.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa post` by
    gvs[] >>
  `32 + 32 * word_size (LENGTH (DROP 32 (hd::tl))) =
     32 * word_size (LENGTH (hd::tl))` by
    (rewrite_tac[LENGTH_DROP] >> irule literal_chunk_span >> simp[]) >>
  `b + offset + 32 < dimword (:256) /\
   b + offset + 32 <= s.vs_alloca_next` by
    (pop_assum (assume_tac o SYM) >> decide_tac) >>
  `w2n ((n2w b:bytes32) + n2w offset) = b + offset` by
    simp[word_add_n2w] >>
  qabbrev_tac `s1 = update_var p (n2w b + n2w offset) s` >>
  qabbrev_tac `s2 = mstore (b + offset) wv s1` >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [data_ptr; Lit (n2w offset)] [p]) s
     = OK s1` by
    (simp[Abbr `s1`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst mid.cs_next_id MSTORE [Var p; Lit wv] []) s1 = OK s2` by
    (simp[Abbr `s2`] >>
     `eval_operand (Var p) s1 = SOME (n2w b + n2w offset)` by
       simp[Abbr `s1`, eval_operand_def, lookup_var_update_var] >>
     drule_then (qspecl_then [`Lit wv`, `wv`, `mid.cs_next_id`] mp_tac) step_MSTORE >>
     simp[eval_operand_def]) >>
  `run_inst_seq (emitted_insts sa post) s = OK s2` by
    gvs[run_inst_seq_def] >>
  `s2.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `s2`, Abbr `s1`, mstore_def, update_var_def] >>
  `(!x. data_ptr = Var x ==> not_fresh_at post x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `eval_operand data_ptr s2 = SOME (n2w b)` by
    (Cases_on `data_ptr` >>
     gvs[Abbr `s2`, Abbr `s1`, eval_operand_def, mstore_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def] >>
     rename1 `Var x` >> `x <> p` by (simp[Abbr `p`] >> metis_tac[LESS_EQ_REFL]) >>
     simp[FLOOKUP_UPDATE]) >>
  first_x_assum (qspecl_then [`s2`, `b`] mp_tac) >>
  impl_tac >- (fs[] >> decide_tac) >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      `run_inst_seq_mem_ok (emitted_insts sa post) s` by
        (qpat_x_assum `emitted_insts sa post = _` SUBST1_TAC >>
         irule literal_chunk_head_mem_ok >> qexists_tac `n2w b` >>
         asm_rewrite_tac[] >> decide_tac) >>
      irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >>
      `s' = s2` by gvs[] >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  qpat_x_assum `run_inst_seq (emitted_insts sa post) s = OK s2`
    (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
  strip_tac >> res_tac >> simp[]
QED

Theorem literal_alloca_frontier[local]:
  run_inst_seq [mk_inst i ALLOCA ops outs] s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  irule step_inst_alloca_alloca_next_mono >>
  qexistsl_tac [`ARB`, `0`, `mk_inst i ALLOCA ops outs`] >>
  simp[step_inst_non_invoke, mk_inst_def, is_alloca_op_def]
QED

(* The whole literal: memory-safe and frontier-monotone. *)
Theorem run_inst_seq_mem_ok_append_run:
  run_inst_seq is1 s = OK s1 /\ run_inst_seq_mem_ok is1 s /\
  run_inst_seq_mem_ok is2 s1 ==> run_inst_seq_mem_ok (is1 ++ is2) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_append >> simp[]
QED

Theorem literal_bytelike_seq_mem:
  !func cenv cx es bs sa sb buf s ctx.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32 + 32 * word_size (LENGTH bs)))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    !t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
        s.vs_alloca_next <= t.vs_alloca_next
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
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = (u,sh)` >>
  Cases_on `u` >>
  rename1 `compile_store_byte_chunks buf.buf_operand bs 32 sh = (v,sb)` >>
  Cases_on `v` >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  qabbrev_tac `sz = 32 + 32 * word_size (LENGTH bs)` >>
  `emitted_insts sa sm =
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sa.cs_next_var)]] /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sm.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh` by
    simp[] >>
  qabbrev_tac `t2 = mstore (w2n w) (n2w (LENGTH bs)) t` >>
  `run_inst_seq (emitted_insts sm sh) t = OK t2` by
    (simp[Abbr `t2`, run_inst_seq_def] >>
     `step_inst_base (mk_inst sm.cs_next_id MSTORE
         [buf.buf_operand; Lit (n2w (LENGTH bs))] []) t =
      OK (mstore (w2n w) (n2w (LENGTH bs)) t)` by
       (irule step_MSTORE >> simp[eval_operand_def]) >>
     gvs[]) >>
  `w2n w + sz <= t.vs_alloca_next` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> simp[]) >>
  `t2.vs_alloca_next = t.vs_alloca_next` by simp[Abbr `t2`, mstore_def] >>
  `eval_operand buf.buf_operand t2 = SOME (n2w (w2n w))` by
    gvs[Abbr `t2`, mstore_def, eval_operand_def, lookup_var_def] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sh x` by
    gvs[not_fresh_at_def] >>
  qspecl_then [`buf.buf_operand`, `bs`, `32`, `sh`, `sb`, `t2`, `w2n w`]
    mp_tac literal_chunks_mem >>
  impl_tac >- (simp[] >> fs[Abbr `sz`]) >> strip_tac >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb =
     emitted_insts sa sm ++ (emitted_insts sm sh ++ emitted_insts sh sb)` by
    (`emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
       (irule emitted_insts_append >> simp[]) >>
     simp[]) >>
  pop_assum SUBST1_TAC >>
  `!x. run_inst_seq (emitted_insts sa sm ++ x) s = run_inst_seq x t` by
    (gen_tac >> irule run_inst_seq_append >> simp[]) >>
  `!x. run_inst_seq (emitted_insts sm sh ++ x) t = run_inst_seq x t2` by
    (gen_tac >> irule run_inst_seq_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (qpat_x_assum `emitted_insts sa sm = _` SUBST1_TAC >>
     simp[run_inst_seq_mem_ok_last, mk_inst_def, below_frontier_no_ranges]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sh) t` by
    (irule emit_mstore_mem_ok >> goal_assum (drule_at Any) >>
     qexists_tac `Lit (n2w (LENGTH bs))` >> fs[Abbr `sz`]) >>
  conj_tac
  >- (`run_inst_seq_mem_ok (emitted_insts sm sh ++ emitted_insts sh sb) t` by
        (irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `t2` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `t` >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule literal_alloca_frontier >> metis_tac[]) >>
  res_tac >> simp[]
QED

(* The memory-mode path, history and frontier of the literal's run. *)
Theorem literal_bytelike_mem_path:
  !func cenv cx es bs sa sb buf s ctx t.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32 + 32 * word_size (LENGTH bs)))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  drule_all literal_bytelike_seq_mem >> strip_tac >>
  drule literal_bytelike_counted_shape >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND3] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> gvs[]
QED

(* The buffer holds the literal's value: the counted run, its value post
   and its store bound. *)
Theorem literal_buffer_mem_run:
  !ctx func cenv cx e es sa sb s0 bs buf tvt v.
    post_value_type cenv e = expr_type e /\
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\
    val_footprint tvt v <= 32 + 32 * word_size (LENGTH bs) /\
    val_store_size tvt v <= 32 + 32 * word_size (LENGTH bs) /\
    (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
             mem_bytes_at (a + 32) (LENGTH bs) mem = bs ==>
             val_in_memory tvt v a mem) /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. gas_path_mem ctx func s0 0 (OK t) /\
      vv_post ctx func cenv cx e es sa sb s0 es (Value v)
        (LocatedValue (expr_type e) (base_ptr buf)) t /\
      eval_operand buf.buf_operand t = SOME w /\
      w2n w + (32 + 32 * word_size (LENGTH bs)) <= t.vs_alloca_next /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  drule_all literal_bytelike_alloca_mem >> strip_tac >>
  drule_all literal_bytelike_run >> strip_tac >>
  drule_all literal_bytelike_mem_path >> strip_tac >>
  drule_all literal_bytelike_gas_path >> strip_tac >>
  `vv_post ctx func cenv cx e es sa sb s0 es (Value v)
     (LocatedValue (expr_type e) (base_ptr buf))
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule literal_memory_vv_post >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac >>
     rpt strip_tac >> res_tac >> fs[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  simp[] >>
  `eval_operand buf.buf_operand
     (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w` by
    (Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  `w2n w + (32 + 32 * word_size (LENGTH bs)) <= t.vs_alloca_next` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> simp[]) >>
  fs[]
QED


(* A non-word expression compiled to a fresh literal buffer holding v. *)
Theorem literal_buffer_vv_sim_mem:
  !ctx func cenv cx ty e es bs tvt v.
    post_value_type cenv e = expr_type e /\
    (!sa vv sb. compile_expr cenv ty e sa = (vv,sb) ==>
       ?buf. vv = LocatedValue (expr_type e) (base_ptr buf) /\
             compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb)) /\
    (!st. eval_expr cx e st = (INL (Value v), st)) /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\
    val_footprint tvt v <= 32 + 32 * word_size (LENGTH bs) /\
    val_store_size tvt v <= 32 + 32 * word_size (LENGTH bs) /\
    (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
             mem_bytes_at (a + 32) (LENGTH bs) mem = bs ==>
             val_in_memory tvt v a mem) /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    (!ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv ==>
           type_memory_size ltv <= 32 + 32 * word_size (LENGTH bs)) ==>
    expr_vv_sim_mem ctx func cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_vv_sim_mem_def] >>
  qpat_x_assum `!sa vv sb. _` drule >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es with gas_obs := []`,
               `sa`, `sb`, `s0`, `bs`, `buf`, `tvt`, `v`]
    mp_tac literal_buffer_mem_run >>
  impl_tac >- simp[] >> strip_tac >>
  fs[vv_post_initial_gas] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value v)`, `es`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def] >>
  simp[vv_store_bound_def, base_ptr_def, read_result_def, return_def] >>
  rw[] >> gvs[] >> res_tac >> decide_tac
QED

Theorem literal_buffer_sim_mem:
  !ctx func cenv cx ty e es bs tvt v.
    post_value_type cenv e = expr_type e /\
    (!sa vv sb. compile_expr cenv ty e sa = (vv,sb) ==>
       ?buf. vv = LocatedValue (expr_type e) (base_ptr buf) /\
             compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb)) /\
    (!st. eval_expr cx e st = (INL (Value v), st)) /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\
    val_footprint tvt v <= 32 + 32 * word_size (LENGTH bs) /\
    val_store_size tvt v <= 32 + 32 * word_size (LENGTH bs) /\
    (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
             mem_bytes_at (a + 32) (LENGTH bs) mem = bs ==>
             val_in_memory tvt v a mem) /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) ==>
    expr_sim_mem ctx func cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_mem_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  qpat_x_assum `!sa vv sb. _` drule >> strip_tac >> gvs[] >>
  simp[unwrap_memory_compile, base_ptr_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es with gas_obs := []`,
               `sa`, `sb`, `s0`, `bs`, `buf`, `tvt`, `v`]
    mp_tac literal_buffer_mem_run >>
  impl_tac >- simp[] >> strip_tac >>
  fs[vv_post_initial_gas] >>
  drule expr_post_of_vv_post_memory >> simp[base_ptr_def] >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `es`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def,
       bind_def, read_result_def, return_def] >>
  simp[expr_store_bound_def] >> rw[] >> gvs[] >> decide_tac
QED

(* A bytes literal of a dynamic bytes type, or a string literal. *)
Theorem literal_other_body_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
    expr_sim_mem ctx func cenv cx ty (Literal ann l) es /\
    expr_vv_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  `(?bs. l = BytesL bs) \/ (?str. l = StringL str)` by
    (gvs[expr_sim_pre_def, well_typed_expr_def] >> Cases_on `l` >> gvs[] >>
     Cases_on `ann` >> gvs[well_typed_literal_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >>
    gvs[is_word_type_def, well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
    rename1 `BytesT (Dynamic n)` >> suspend "bytes") >>
  rename1 `StringT n` >> suspend "string"
QED

Resume literal_other_body_mem[bytes]:
  gvs[alloc_limits_expr_def, literal_alloc_ok_def, compatible_bound_def] >>
  `32 + 32 * word_size (LENGTH bs) < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  assume_tac (Q.SPEC `n` le_word_size_mul) >>
  assume_tac (Q.SPEC `LENGTH (bs:word8 list)` le_word_size_mul) >>
  `!sa vv sb.
     compile_expr cenv ty (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) sa =
       (vv,sb) ==>
     ?buf. vv = LocatedValue (BaseT (BytesT (Dynamic n))) (base_ptr buf) /\
           compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb)` by
    (rpt gen_tac >>
     simp[compile_expr_def, compile_literal_vv_def, expr_type_def,
          is_word_type_def, comp_bind_def, comp_return_def] >>
     Cases_on `compile_bytelike_literal bs (LENGTH bs) sa` >> simp[]) >>
  `!st. eval_expr cx (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) st =
        (INL (Value (BytesV bs)), st)` by
    simp[Once evaluate_def, return_def, evaluate_literal_def] >>
  conj_tac
  >- (irule literal_buffer_sim_mem >>
      conj_tac >- simp[expr_type_def, is_word_type_def] >>
      conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qexistsl_tac [`bs`, `BaseTV (BytesT (Dynamic n))`, `BytesV bs`] >>
      fs[expr_type_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
         val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def,
         type_memory_size_def, lowered_value_type_def] >>
      rpt conj_tac >> decide_tac) >>
  irule literal_buffer_vv_sim_mem >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qexistsl_tac [`bs`, `BaseTV (BytesT (Dynamic n))`, `BytesV bs`] >>
  fs[expr_type_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
     val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def,
     type_memory_size_def, lowered_value_type_def] >>
  rpt conj_tac >> decide_tac
QED

Resume literal_other_body_mem[string]:
  gvs[alloc_limits_expr_def, literal_alloc_ok_def, well_formed_type_def,
      vyperValueTheory.evaluate_type_def] >>
  `32 + 32 * word_size (LENGTH str) < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  assume_tac (Q.SPEC `n` le_word_size_mul) >>
  assume_tac (Q.SPEC `LENGTH (str:string)` le_word_size_mul) >>
  `!sa vv sb.
     compile_expr cenv ty (Literal (BaseT (StringT n)) (StringL str)) sa =
       (vv,sb) ==>
     ?buf. vv = LocatedValue (BaseT (StringT n)) (base_ptr buf) /\
           compile_bytelike_literal (MAP (n2w o ORD) str) (LENGTH str) sa =
             (buf,sb)` by
    (rpt gen_tac >>
     simp[compile_expr_def, compile_literal_vv_def, expr_type_def,
          is_word_type_def, comp_bind_def, comp_return_def] >>
     Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) (LENGTH str) sa` >>
     simp[]) >>
  `!st. eval_expr cx (Literal (BaseT (StringT n)) (StringL str)) st =
        (INL (Value (StringV str)), st)` by
    simp[Once evaluate_def, return_def, evaluate_literal_def] >>
  conj_tac
  >- (irule literal_buffer_sim_mem >>
      conj_tac >- simp[expr_type_def, is_word_type_def] >>
      conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qexistsl_tac [`MAP (n2w o ORD) str`, `BaseTV (StringT n)`, `StringV str`] >>
      fs[expr_type_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
         val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def,
         type_memory_size_def, LET_THM, lowered_value_type_def] >>
      rpt conj_tac >> decide_tac) >>
  irule literal_buffer_vv_sim_mem >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qexistsl_tac [`MAP (n2w o ORD) str`, `BaseTV (StringT n)`, `StringV str`] >>
  fs[expr_type_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
     val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def,
     type_memory_size_def, LET_THM, lowered_value_type_def] >>
  rpt conj_tac >> decide_tac
QED

Finalise literal_other_body_mem

Theory bodyEmptyBufferMemory
Ancestors
  builtinSimple exprSimBufferEmptyExec bodyLiteralBufferMemory
  abiEmptySequence abiEmptyAllocate exprLoweringProps emitHelperProps freshWrites
  allocaFootprint allocLimits exprSimAlloc venomMemDefs venomMemProps
  fragExec fragGasSeqMem fragGasPathMem allocaHistoryFragment gasSummary
  fragExecMem instMemFrontier venomExecSemantics venomState venomInst
  compileEnv context emitHelper finite_map words list rich_list arithmetic

Theorem compile_zero_words_seq_mem:
  !n pop sa sb s w.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!x. pop = Var x ==> not_fresh_at sa x) /\
    w2n w + 32*n <= s.vs_alloca_next /\
    w2n w + 32*n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      t.vs_alloca_next = s.vs_alloca_next /\ eval_operand pop t = SOME w)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def,
    emitted_insts_def, run_inst_seq_mem_ok_def, run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_zero_words _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_zero_words_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words pop n sa = (ignored,sm)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum (qspecl_then [`pop`, `sa`, `sm`, `s`, `w`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND, LESS_EQ_ADD]) >>
  `LENGTH sa.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `LENGTH sa.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (simp[emitted_insts_def, DROP_APPEND, LENGTH_APPEND, SUB_EQ_0]) >>
  `emitted_insts sm sb =
    [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))]
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst cs''.cs_next_id MSTORE [dst; Lit 0w] []]` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `!t. run_inst_seq (emitted_insts sa sm) s = OK t ==>
     run_inst_seq_mem_ok (emitted_insts sm sb) t /\
     (!u. run_inst_seq (emitted_insts sm sb) t = OK u ==>
       u.vs_alloca_next = s.vs_alloca_next /\ eval_operand pop u = SOME w)` by
    (gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >>
     qabbrev_tac `p = STRING #"%" (toString sm.cs_next_var)` >>
     `step_inst_base (mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))] [p]) t =
       OK (update_var p (w + n2w (32*n)) t)` by
       (irule step_ADD >> simp[eval_operand_def]) >>
     `w2n (w + n2w (32*n)) = w2n w + 32*n` by
       (`w2n w + 32*n < dimword (:256)` by decide_tac >>
        `32*n < dimword (:256)` by decide_tac >>
        simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
     conj_tac
     >- (asm_rewrite_tac[] >>
         simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
           below_frontier_MSTORE, eval_operand_def, lookup_var_update_var,
           update_var_def] >>
         simp[mk_inst_def, below_frontier_no_ranges, lookup_var_def,
           FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >> decide_tac) >>
     `step_inst_base (mk_inst cs''.cs_next_id MSTORE [Var p; Lit 0w] [])
        (update_var p (w + n2w (32*n)) t) =
        OK (mstore (w2n (w + n2w (32*n))) 0w
          (update_var p (w + n2w (32*n)) t))` by
       (irule step_MSTORE >> simp[eval_operand_def, lookup_var_update_var]) >>
     gen_tac >> disch_tac >>
     `u = mstore (w2n (w + n2w (32*n))) 0w
          (update_var p (w + n2w (32*n)) t)` by
       (qpat_x_assum `run_inst_seq (emitted_insts sm sb) t = OK u` mp_tac >>
        gvs[] >> simp[run_inst_seq_def]) >>
     conj_tac >- simp[mstore_def, update_var_def] >>
     Cases_on `pop` >>
     gvs[eval_operand_def, mstore_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, not_fresh_at_def, Abbr `p`] >>
     NO_TAC) >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      irule run_inst_seq_mem_ok_append >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> gvs[]) >>
  gen_tac >> disch_tac >>
  Cases_on `run_inst_seq (emitted_insts sa sm) s`
  >- (drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` assume_tac) >>
      gvs[] >> metis_tac[]) >>
  `!u. run_inst_seq (emitted_insts sa sm) s <> OK u` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `emitted_insts sm sb` assume_tac) >> gvs[]
QED

Theorem compile_zero_words_no_gas:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [Once compile_zero_words_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words pop n sa = (ignored,sm)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND, LESS_EQ_ADD]) >>
  `LENGTH sa.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `LENGTH sa.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++
    [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))]
      [STRING #"%" (toString sm.cs_next_var)];
     mk_inst cs''.cs_next_id MSTORE [dst; Lit 0w] []]` by
    simp[emitted_insts_def, DROP_APPEND, LENGTH_APPEND] >>
  asm_rewrite_tac[] >> simp[mk_inst_def]
QED

Theorem compile_empty_buffer_seq_mem:
  !sz header sa sb buf func cenv cx es s ctx.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      s.vs_alloca_next <= t.vs_alloca_next) /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_empty_complex_parts >> strip_tac >>
  rename1 `compile_alloc_buffer sz sa = (buf,sm)` >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]] /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sm.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> simp[]) >>
  `w2n w + sz <= t.vs_alloca_next` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK t` mp_tac >>
     asm_rewrite_tac[run_inst_seq_def] >>
     simp[AllCaseEqs()] >> strip_tac >>
     irule step_inst_alloca_alloca_next_mono >>
     qexistsl_tac [`ARB`, `0`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_alloca_op_def]) >>
  `sm.cs_current_insts ++ emitted_insts sm sb = sb.cs_current_insts /\
   run_inst_seq_mem_ok (emitted_insts sm sb) t /\
   (!u. run_inst_seq (emitted_insts sm sb) t = OK u ==>
      u.vs_alloca_next = t.vs_alloca_next) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm sb)` by
    (Cases_on `header` >> fs[]
     >- (drule emitted_insts_emit_void >> strip_tac >>
         `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
           (irule emit_mstore_mem_ok >> goal_assum (drule_at Any) >>
            qexists_tac `Lit 0w` >> simp[] >> decide_tac) >>
         `step_inst_base (mk_inst sm.cs_next_id MSTORE [buf.buf_operand; Lit 0w] []) t =
           OK (mstore (w2n w) 0w t)` by
           (irule step_MSTORE >> simp[eval_operand_def]) >>
         gvs[] >> simp[run_inst_seq_def, mstore_def, mk_inst_def]) >>
     `32 * ((sz+31) DIV 32) = sz` by
       (`sz = (sz DIV 32) * 32` by
          (qspec_then `32` mp_tac DIVISION >> simp[] >>
           disch_then (qspec_then `sz` mp_tac) >> decide_tac) >>
        pop_assum SUBST1_TAC >> simp[ADD_DIV_ADD_DIV]) >>
     drule abi_empty_zero_words_shape >> strip_tac >>
     drule compile_zero_words_no_gas >> strip_tac >>
     drule compile_zero_words_seq_mem >>
     disch_then (qspecl_then [`t`, `w`] mp_tac) >>
     impl_tac >- simp[] >>
     fs[inst_extends_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `!xs. run_inst_seq (emitted_insts sa sm ++ xs) s = run_inst_seq xs t` by
    (gen_tac >> irule run_inst_seq_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    simp[run_inst_seq_mem_ok_last, mk_inst_def, below_frontier_no_ranges] >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> res_tac >> simp[]) >>
  asm_rewrite_tac[] >> simp[mk_inst_def]
QED

Theorem compile_empty_buffer_mem_path:
  !sz header sa sb buf func cenv cx es s ctx t.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_empty_complex_parts >> strip_tac >>
  rename1 `compile_alloc_buffer sz sa = (buf,sm)` >>
  drule abi_empty_alloc_buffer_shape >> strip_tac >>
  drule abi_empty_initializer_shape >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `sm.cs_blocks = sa.cs_blocks /\ sm.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `fn_has_code sa sm func` by
    (mp_tac fn_has_code_split >>
     disch_then (qspecl_then [`sa`, `sm`, `sb`, `func`] mp_tac) >>
     impl_tac >- (fs[cs_extends_def, inst_extends_def, IS_PREFIX_APPEND] >>
                  metis_tac[APPEND_ASSOC, APPEND_11]) >> simp[]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all compile_empty_buffer_seq_mem >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qpat_x_assum `_ = sm.cs_current_insts ++ _` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac[emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     pure_rewrite_tac[DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[IS_PREFIX_APPEND, emitted_insts_def] >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND3] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL]) >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> gvs[]
QED

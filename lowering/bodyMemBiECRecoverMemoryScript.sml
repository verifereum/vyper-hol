(* Memory checks for ECRecover's finite instruction sequence. *)
Theory bodyMemBiECRecoverMemory
Ancestors
  exprSimPrecompiles exprSimDefs exprSimProps exprLowering exprLoweringProps
  exprSimWordArgs exprSimHypsDefs vyperTyping vyperAST vyperTypeSystem
  compileEnv loweringStateRelDefs list rich_list builtinMisc loweringPosts exprBopLowering
  vyperInterpreter vyperState vyperContext vyperValue vyperTypeInvariants
  valueEncoding integer_word words byte exprSimAlloc exprSimLiteralBuffer
  exprSimOps emitHelper emitHelperProps fragExec venomExecSemantics
  venomMemDefs venomState venomInst ASCIInumbers dftCommutation
  abiDecodeStaticProps immutableMemoryFrame valueEncodingProps context
  loweringHalt venomCallOracleDefs extCallOracle bodyMemBiECRecoverRun
  allocaFootprint bodyLiteralBufferMemory fragExecMem instMemFrontier
  memSafeRun
Libs
  monadsyntax

Theorem ecrecover_input_stores_mem:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig] od) sa = ((),sb) /\
  eval_operand base_op s = SOME p /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) /\
  w2n p + 128 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!q k z t. MEM q [base_op;h;v;r;sig] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule ecrecover_operand_generated_update >>
     simp[] >> metis_tac[]) >>
  `w2n (p+32w) = w2n p + 32 /\
   w2n (p+64w) = w2n p + 64 /\
   w2n (p+96w) = w2n p + 96` by
    (rpt conj_tac >> irule w2n_add_n2w_lt >> decide_tac) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       eval_operand_def, lookup_var_update_var, ecrecover_operand_mstore,
       inst_dload_in_section_def, mk_inst_def]
QED

(* The existing allocator semantics covers both cached and fresh sites. *)
Theorem ecrecover_alloc_mem:
  context$compile_alloc_buffer sz sa = (buf,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    w2n w + sz < dimword (:256) /\
    w2n w + sz <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  conj_tac
  >- (drule compile_alloc_buffer_insts >> strip_tac >>
      simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
           run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  qexistsl_tac [`t`,`w`] >> simp[] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> simp[]
QED

Theorem ecrecover_buffers_mem_ready:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  run_inst_seq_mem_ok (emitted_insts sf sm) s /\
  ?t wi wo. run_inst_seq (emitted_insts sf sm) s = OK t /\
    eval_operand ip t = SOME wi /\ eval_operand op t = SOME wo /\
    w2n wi + 128 <= t.vs_alloca_next /\
    w2n wo + 32 <= t.vs_alloca_next
Proof
  strip_tac >> drule_all ecrecover_buffers_prefix_shape >> strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sm)` kall_tac >>
  `128 < dimword (:256) /\ 32 < dimword (:256)` by
    simp[wordsTheory.dimword_def] >>
  qpat_assum `context$compile_alloc_buffer 128 sf = (ib,sa)`
    (mp_then Any (drule_all_then strip_assume_tac) literal_alloc_buffer_run) >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  rename1 `eval_operand ib.buf_operand s1 = SOME wi` >>
  `w2n wi + 128 <= s1.vs_alloca_next` by
    (`alloca_inv s1` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `s1.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `!z. MEM z [h;v;r;sig] ==> eval_operand z s1 = eval_operand z s` by
    (rpt strip_tac >> Cases_on `z` >> simp[eval_operand_def] >>
     first_x_assum irule >> first_x_assum irule >> simp[]) >>
  `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
   eval_operand r s1 = SOME wr /\ eval_operand sig s1 = SOME ws` by
    metis_tac[listTheory.MEM] >>
  `!x. MEM (Var x) [ib.buf_operand;h;v;r;sig] ==> not_fresh_at sa x` by
    (qpat_x_assum `!x. MEM (Var x) [h;v;r;sig] ==> _` mp_tac >>
     qpat_x_assum `context$compile_alloc_buffer 128 sf = (ib,sa)`
       (mp_tac o MATCH_MP compile_alloc_buffer_parts) >>
     POP_ASSUM_LIST (K all_tac) >> simp[listTheory.MEM] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s1` by
    (irule ecrecover_input_stores_mem >> goal_assum (drule_at Any) >> simp[]) >>
  `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  `cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n wi) 128 off (type_memory_size tv)` by
    (match_mp_tac (Q.INST
       [`s` |-> `s1`, `inst` |-> `mk_inst sf.cs_next_id ALLOCA [Lit 128w]
         [STRING #"%" (toString sf.cs_next_var)]`]
       precompile_alloca_immutable_disjoint) >> simp[mk_inst_def]) >>
  `!aid b len. aid < sf.cs_next_id /\
     FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n wi) 128 b len` by
    (rpt strip_tac >>
     `alloca_inv s1` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`sf.cs_next_id`,`aid`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  drule_all ecrecover_input_stores_sim >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s1 = OK s2` >>
  drule_all ecrecover_alloc_mem >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sc) s2 = OK s3` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME wo` >>
  qpat_assum `stmt_state_rel ctx func cenv cx es s2`
    (mp_then Any (drule_all_then strip_assume_tac) literal_alloc_buffer_run) >>
  gvs[] >>
  `s2.vs_allocas = s1.vs_allocas` by
    (qpat_x_assum `(s2 with <|vs_memory := m; vs_vars := vs|>) = s1`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `FLOOKUP s3.vs_allocas sf.cs_next_id = SOME (w2n wi,128)` by
    (qpat_x_assum `!aid entry. _ ==> FLOOKUP s3.vs_allocas aid = SOME entry` irule >>
     simp[]) >>
  `w2n wi + 128 <= s3.vs_alloca_next` by
    (`alloca_inv s3` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `eval_operand ib.buf_operand s3 = SOME wi` by
    (simp[eval_operand_def] >>
     qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x s2 = _`
       (qspec_then `p` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sb x ==> lookup_var x s3 = _`
       (qspec_then `p` mp_tac) >>
     `not_fresh_at sa p` by simp[] >>
     `not_fresh_at sb p` by fs[not_fresh_at_def] >>
     fs[eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sc sm) s3` by
    (drule_all allocaFootprintTheory.emit_mstore_mem_ok >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sf sa) s` by
    (qpat_assum `context$compile_alloc_buffer 128 sf = (ib,sa)`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
          run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sf sm = _` SUBST1_TAC >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `s1` >> conj_tac >- first_assum ACCEPT_TAC >>
      irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `s2` >> conj_tac >- first_assum ACCEPT_TAC >>
      irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `s3` >> simp[]) >>
  `run_inst_seq (emitted_insts sc sm) s3 = OK (mstore (w2n w) 0w s3)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def]) >>
  qexistsl_tac [`mstore (w2n w) 0w s3`, `wi`, `w`] >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sf sm = _` SUBST1_TAC >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      imp_res_tac run_inst_seq_append >> simp[]) >>
  simp[ecrecover_operand_mstore] >> simp[mstore_def] >> gvs[]
QED

Theorem ecrecover_suffix_mem:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success]; emit_op MLOAD [op] od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  w2n wi + 128 <= s.vs_alloca_next /\
  w2n wo + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >> drule ecrecover_suffix_shape >> strip_tac >>
  `!q k z t. (q = ip \/ q = op) /\ sm.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule ecrecover_operand_generated_update >>
     simp[] >> metis_tac[]) >>
  `!q t rs. eval_operand q (t with vs_gas_readings := rs) = eval_operand q t` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `!q rq a n t. eval_operand q (SND (consume_call_outcome rq a n t)) =
     eval_operand q t` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `!x v t. (update_var x v t).vs_alloca_next = t.vs_alloca_next` by
    simp[update_var_def] >>
  `!rq a n t. (SND (consume_call_outcome rq a n t)).vs_alloca_next =
      t.vs_alloca_next` by simp[] >>
  `!q k z t rs. (q = ip \/ q = op) /\ sm.cs_next_var <= k ==>
      eval_operand q ((update_var (STRING #"%" (toString k)) z t)
        with vs_gas_readings := rs) = eval_operand q t` by
    (rpt strip_tac >> simp[]) >>
  qpat_x_assum `emitted_insts sm sb = _` SUBST1_TAC >>
  Cases_on `s.vs_gas_readings` >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, bind_outputs_def,
       inst_dload_in_section_def, exec_gas_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_STATICCALL,
       wordsTheory.dimword_def,
       eval_operand_def, lookup_var_update_var] >>
  pure_rewrite_tac[GSYM update_var_def] >>
  FIRST [simp[step_inst_base_def, mk_inst_def, eval_operand_def,
       lookup_var_update_var, exec_ext_call_def, inst_dload_in_section_def,
       Excl "consume_call_outcome_eq", pairTheory.UNCURRY_DEF]] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  simp[Excl "consume_call_outcome_eq"] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       Excl "consume_call_outcome_eq"] >>
  simp[NoAsms, step_inst_base_def, mk_inst_def, eval_operand_def,
       lookup_var_update_var, Excl "consume_call_outcome_eq",
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  pure_rewrite_tac[COND_RAND, COND_RATOR] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD,
       Excl "consume_call_outcome_eq"]
QED

Theorem ecrecover_buffers_mem:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  run_inst_seq_mem_ok (emitted_insts sf sm) s
Proof
  strip_tac >> drule_all ecrecover_buffers_mem_ready >> simp[]
QED

Theorem compile_ecrecover_mem_ok:
  compile_ecrecover h v r sig sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  run_inst_seq_mem_ok (emitted_insts sf sb) s
Proof
  strip_tac >> drule compile_ecrecover_split >> strip_tac >>
  drule ecrecover_suffix_shape >> strip_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND] >> simp[]) >>
  drule_all ecrecover_buffers_mem_ready >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sm) s = OK t` >>
  `(!y. ip = Var y ==> not_fresh_at sm y) /\
   (!y. op = Var y ==> not_fresh_at sm y)` by
    (drule_all ecrecover_buffers_prefix_shape >> strip_tac >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (drule_all ecrecover_suffix_mem >> simp[]) >>
  `LENGTH sf.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0] >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append_run >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `run_inst_seq_mem_ok (emitted_insts sm sb) t` mp_tac >>
  asm_rewrite_tac[]
QED

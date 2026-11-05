(* Memory checks for ECRecover's finite instruction sequence. *)
Theory bodyMemBiECRecoverMemory
Ancestors
  bodyMemBiECRecoverStores bodyMemBiECRecoverBuffers
  bodyMemBiECRecoverSuffix bodyMemBiECRecoverRun
  exprSimAlloc loweringHalt allocaFootprint exprSimWordArgs valueEncodingProps
  exprSimPrecompiles bodyLiteralBufferMemory
  fragExecMem instMemFrontier memSafeRun exprSimDefs exprSimProps exprLoweringProps
  compileEnv context emitHelper emitHelperProps abiDecodeStaticProps
  venomExecSemantics venomMemDefs venomState venomInst
  words rich_list list
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
     simp[compileEnvTheory.regions_disjoint_def]) >>
  drule_all ecrecover_input_stores_sim >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s1 = OK s2` >>
  drule_all ecrecover_alloc_mem >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sc) s2 = OK s3` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME wo` >>
  `run_inst_seq_mem_ok (emitted_insts sc sm) s3` by
    (drule_all allocaFootprintTheory.emit_mstore_mem_ok >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sf sa) s` by
    (qpat_assum `context$compile_alloc_buffer 128 sf = (ib,sa)`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
          run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  qpat_x_assum `emitted_insts sf sm = _` SUBST1_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `s1` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `s2` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule run_inst_seq_mem_ok_append_run >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `s3` >> simp[]
QED

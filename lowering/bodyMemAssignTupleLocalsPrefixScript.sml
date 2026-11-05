(* Memory-checked staging and load prefix of tuple-local assignment. *)
Theory bodyMemAssignTupleLocalsPrefix
Ancestors
  bodyMemAssignTupleLocalsPrep bodyDeclMemoryCore bodyDeclMemoryCounted
  exprSimAlloc exprSimBufferStore abiBuiltinAllocation tupleStageProps
  fragGasPathMem fragGasMode fragGasSeqMem allocaHistoryFragment
  exprLoweringProps loweringSlice emitHelper emitHelperProps exprLowering
  compileEnv context venomState venomExecSemantics venomInst freshWrites
  valueEncoding valueEncodingProps valueTypingMemoryProps finite_map list
  localPtrsProps stmtSimDefs stmtSimProps fragExec fragExecMem bodyMemoryDefs
  loweringPosts vyperTyping
Libs
  monadsyntax

(* Snapshot execution retains its allocation witness even on loop re-entry. *)
Theorem tuple_scratch_run_allocation[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  run_inst_seq (emitted_insts sa sm) s = OK a /\
  run_inst_seq (emitted_insts sm sn) a = OK t ==>
  ?w. eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  `a.vs_labels = s.vs_labels` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a` mp_tac >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (simp[LET_THM, update_var_def] >> rpt strip_tac >> gvs[]) >>
     PairCases_on `x` >> simp[LET_THM, update_var_def] >> rpt strip_tac >> gvs[]) >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `n < dimword (:256)` by decide_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >> gvs[] >>
  `sm.cs_next_var = sn.cs_next_var` by
    metis_tac[buffer_copy_memory_shape] >>
  qexists_tac `w` >>
  Cases_on `n = 0` >>
  gvs[mcopy_def, write_memory_with_expansion_def, LET_THM,
      eval_operand_def, lookup_var_def, not_fresh_at_def]
QED

Theorem tuple_scratch_path_mem:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
    return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    w2n w + n <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >> drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  drule_all tuple_scratch_run_allocation >> strip_tac >> gvs[] >>
  `run_inst_seq (emitted_insts sa sn) s = OK t` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  `return_buf_frame d ce sn t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sn)` by
    metis_tac[body_scratch_prefix_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sn)` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sn.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx] >> conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >>
  Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem tuple_container_frontier:
  stmt_state_rel ctx func ce cx es s /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region ce es.scopes s name b sz)) ==>
  b + sz <= s.vs_alloca_next
Proof
  strip_tac
  >- (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  fs[local_region_def] >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem tuple_stage_copy_path_mem:
  (do buf <- compile_alloc_buffer n;
      emit_void MCOPY [buf.buf_operand; op; Lit (n2w n)];
      comp_return buf.buf_operand od) sa = (staged,sb) /\
  0 < n /\ n < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
    return_buf_frame d ce sb t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    eval_operand staged t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    w2n w + n <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    (!x. staged = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >>
  qpat_x_assum `(do _ od) sa = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer n sa` >>
  rename1 `compile_alloc_buffer n sa = (buf,sm)` >>
  Cases_on `emit_void MCOPY [buf.buf_operand; op; Lit (n2w n)] sm` >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_void MCOPY _ sm = ((),sb)` >>
  `compile_copy_memory buf.buf_operand op n sm = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  drule_all (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] tuple_scratch_path_mem) >> simp[]
QED

Theorem optional_tuple_stage_path_mem:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw d.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) sa = (staged,sb) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) se sa es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME sw /\
    0 < type_memory_size_list tvs /\
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w. eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?b sz. b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es.scopes t name b sz))) /\
      gas_path_mem ctx func s 0 (OK t) /\
      alloca_history func t /\ return_buf_frame d cenv sb t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      w2n w + type_memory_size_list tvs <= t.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all expr_tuple_memory_owned >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  `b + sz <= s.vs_alloca_next` by
    (irule tuple_container_frontier >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[]) >>
  `w2n sw + type_memory_size_list tvs <= s.vs_alloca_next` by decide_tac >>
  `values_have_types tvs vs` by gvs[value_has_type_def] >> simp[] >>
  Cases_on `flag`
  >- (qpat_x_assum `b <= w2n sw` kall_tac >> gnvs[] >>
      `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
       val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
       val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <=
         type_memory_size_list tvs` by
        simp[val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def] >>
      `type_memory_size_list tvs + w2n sw <= s.vs_alloca_next` by decide_tac >>
      drule_all (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] tuple_stage_copy_path_mem) >>
      disch_then (qx_choosel_then [`t`, `w`] strip_assume_tac) >>
      qexistsl_tac [`t`, `w`] >> simp[] >>
      conj_tac >- gvs[val_in_memory_def] >>
      qexistsl_tac [`w2n w`, `type_memory_size_list tvs`] >> simp[] >> metis_tac[]) >>
  gvs[comp_return_def] >> qexistsl_tac [`s`, `sw`] >> simp[cj 1 gas_path_mem_rules] >>
  qexistsl_tac [`b`, `sz`] >> simp[] >> metis_tac[]
QED

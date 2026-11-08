(* Memory-checked staging and load prefix of tuple-local assignment. *)
Theory bodyMemAssignTupleLocalsPrefix
Ancestors
  bodyMemAssignTupleLocalsPrep bodyDeclMemoryCore bodyDeclMemoryCounted
  exprSimAlloc exprSimBufferStore abiBuiltinAllocation tupleStageProps
  fragGasPathMem fragGasMode fragGasSeqMem allocaHistoryFragment
  exprLoweringProps loweringSlice emitHelper emitHelperProps exprLowering
  compileEnv context venomState venomExecSemantics venomInst freshWrites
  valueEncoding valueEncodingProps valueTypingMemoryProps finite_map list rich_list
  localPtrsProps stmtSimDefs stmtSimProps fragExec fragExecMem bodyMemoryDefs
  loweringPosts vyperTyping instMemFrontier stmtSimReturn tupleLoadProps stmtLowering tupleTypedLoad
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
     qpat_assum `emitted_insts sa sm = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [run_inst_seq_def, step_inst_base_def, mk_inst_def,
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

(* Memory check for the ADD / optional MLOAD head used by tupleLoadProps. *)
Theorem tuple_elem_load_head_mem_ok[local]:
  emit_op ADD [bop; Lit off] sa = (pv, sm) /\
  compile_load_memory pv load sm = (v, sb) /\
  eval_operand bop s = SOME w /\
  (load ==> w2n (w + off) + 32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `load` >>
  gvs[contextTheory.compile_load_memory_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, DROP_APPEND1, venomInstTheory.mk_inst_def,
       run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_no_ranges, below_frontier_MLOAD] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def,
       bind_outputs_def, lookup_var_update_var] >>
  gvs[eval_operand_def] >>
  simp[GSYM venomInstTheory.mk_inst_def, below_frontier_MLOAD,
       eval_operand_def, lookup_var_update_var, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem compile_tuple_load_all_mem_ok:
  !tys cenv bop off sa elems sb s w.
    compile_tuple_load_all cenv bop tys off sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    EVERY (\ty. is_word_type ty ==> 32 <= type_memory_bytes cenv ty) tys /\
    w2n w + off + SUM (MAP (type_memory_bytes cenv) tys) < dimword (:256) /\
    w2n w + off + SUM (MAP (type_memory_bytes cenv) tys) <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct
  >- simp[compile_tuple_load_all_def, comp_return_def, emitted_insts_def,
          run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `compile_load_memory _ _ sm = (v,sh)` >>
  rename1 `compile_tuple_load_all _ _ _ _ sh = (rest,sf)` >>
  drule_all tuple_elem_load_head_run >> strip_tac >> gvs[] >>
  `w2n (w + n2w off) = w2n w + off` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sh) s` by
    (irule tuple_elem_load_head_mem_ok >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_load_memory _ _ _ = _`)) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `(!x. bop = Var x ==> not_fresh_at sh x) /\
   eval_operand bop (s with vs_vars := vs) = SOME w` by
    (conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >>
       qexists `sa` >> simp[]) >>
     `eval_operand bop (s with vs_vars := vs) = eval_operand bop s` by
       (irule eval_operand_old_vars >> simp[] >> qexists `sa` >> simp[]) >> simp[]) >>
  `sf.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sf /\
   same_blocks sh sf` by
    (drule_all compile_tuple_load_all_run >> simp[]) >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >>
  goal_assum (drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)) >>
  simp[] >> decide_tac
QED

Theorem compile_tuple_load_all_no_gas[local]:
  !tys cenv bop off sa elems sb.
    compile_tuple_load_all cenv bop tys off sa = (elems,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct
  >- simp[compile_tuple_load_all_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `compile_load_memory _ _ sm = (v,sh)` >>
  rename1 `compile_tuple_load_all _ _ _ _ sh = (rest,sf)` >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sh)` by
    (Cases_on `is_word_type h` >>
     gvs[contextTheory.compile_load_memory_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     simp[emitted_insts_def, DROP_APPEND1, venomInstTheory.mk_inst_def]) >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    (irule emitted_insts_append >> simp[]) >>
  simp[]
QED

Theorem compile_tuple_load_all_path_mem:
  !tys cenv bop off sa elems sb s w ctx func t.
    compile_tuple_load_all cenv bop tys off sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    EVERY (\ty. is_word_type ty ==> 32 <= type_memory_bytes cenv ty) tys /\
    w2n w + off + SUM (MAP (type_memory_bytes cenv) tys) < dimword (:256) /\
    w2n w + off + SUM (MAP (type_memory_bytes cenv) tys) <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_tuple_load_all_mem_ok >> strip_tac >>
  drule_all compile_tuple_load_all_run >> strip_tac >>
  drule compile_tuple_load_all_no_gas >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND3] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_FILTER, FILTER_EQ_NIL, EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> gvs[]
QED

Theorem tuple_load_typed_layout[local]:
  !tys tvs tenv cenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs ==>
    SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs /\
    EVERY (\ty. is_word_type ty ==> 32 <= type_memory_bytes cenv ty) tys
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> simp[] >>
  drule_all word_type_sizes >> simp[]
QED

Theorem compile_tuple_load_all_typed_path_mem:
  !tys tvs vals tenv cenv bop sa elems sb s w ctx func cx es d.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    w2n w + type_memory_size_list tvs <= s.vs_alloca_next /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\ local_ptrs_reserved cenv sb /\
    ?t. stmt_state_rel ctx func cenv cx es t /\
      gas_path_mem ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t /\ return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_load_typed_layout >> strip_tac >>
  drule_all compile_tuple_load_all_typed_run >> strip_tac >>
  drule_all tuple_load_run_lift >> strip_tac >>
  `gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule compile_tuple_load_all_path_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)) >>
     qexists `w` >> simp[arithmeticTheory.ADD_COMM]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `return_buf_frame d cenv sb (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[] >> rpt strip_tac >> gvs[lookup_var_def]) >>
  simp[] >> qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> conj_tac >- fs[same_blocks_def] >>
  conj_tac >- gvs[] >>
  conj_tac >- (rpt strip_tac >> gvs[lookup_var_def]) >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

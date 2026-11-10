(* Full-frame counted allocation, valid also at reused ALLOCA sites. *)
Theory bodyMemAggregateAlloc
Ancestors
  bodyMemAggregateBounds bodyAllocMemory fragGasSeqMem
  exprSimAggregateLoops exprSimAggregateChildren exprSimAlloc
  exprSimHyps exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq fragExec
  exprLowering exprLoweringProps compileEnv loweringStateRelDefs valueEncoding
  vyperInterpreter vyperState abiBuiltinAllocation allocaHistoryFragment
  emitHelperProps emitHelper context rich_list list venomInst

Theorem aggregate_alloc_buffer_history_any_block:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem aggregate_buffer_alloc_counted_mem_any_block:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s0 ==>
  ?inst x t b. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path T ctx func s0 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    lookup_var x t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    (!aid p n. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n <=>
      local_region ce es.scopes s0 name p n) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    b + sz <= t.vs_alloca_next
Proof
  strip_tac >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq _ s0 = OK u` >>
  `emitted_insts sa sm =
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]] /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sm)
          (DROP s0.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s0` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_last] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >>
     simp[venomInstTheory.mk_inst_def]) >>
  `gas_path_mem ctx func s0 0
     (OK (u with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (drule_all run_inst_seq_gas_path_mem >>
     simp[venomInstTheory.mk_inst_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb` by
    (qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [ai]` >>
     `step_inst 0 ctx ai s0 = OK u` by
       (fs[run_inst_seq_def, venomExecSemanticsTheory.step_inst_non_invoke,
           Abbr `ai`, venomInstTheory.mk_inst_def, AllCaseEqs()]) >>
     `~is_terminator ai.inst_opcode` by
       simp[Abbr `ai`, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def] >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >>
     drule_all venomInstProofsTheory.step_preserves_halted >> simp[]) >>
  `!name p n. local_region ce es.scopes u name p n <=>
               local_region ce es.scopes s0 name p n` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (irule aggregate_alloc_buffer_history_any_block >>
     simp[] >> qexistsl [`buf`, `sz`, `s0`, `sa`] >>
     simp[] >> fs[stmt_state_rel_def]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >>
     simp[run_inst_seq_def, Once venomExecSemanticsTheory.step_inst_base_def,
          venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_alloca_def,
          venomStateTheory.eval_operand_def] >>
     Cases_on `FLOOKUP s0.vs_allocas sa.cs_next_id` >>
     simp[venomStateTheory.update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `w2n w + sz <= u.vs_alloca_next` by
    (drule_all aggregate_alloca_capacity_mem >> simp[]) >>
  qexistsl_tac [`inst`, `x`, `u with vs_inst_idx := LENGTH sm.cs_current_insts`,
                `w2n w`] >>
  gvs[gas_marked_path_def, stmt_state_rel_inst_idx,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, local_region_def,
      wordsTheory.n2w_w2n] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  rpt gen_tac >>
  qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _`
    (qspecl_then [`name`, `p'`, `n`] mp_tac) >> simp[]
QED

(* Backwards-compatible open-block interface. *)
Theorem aggregate_buffer_alloc_counted_mem:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s0 /\ ~block_is_terminated sa ==>
  ?inst x t b. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path T ctx func s0 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    lookup_var x t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    (!aid p n. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n <=>
      local_region ce es.scopes s0 name p n) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    b + sz <= t.vs_alloca_next
Proof
  strip_tac >> drule_all aggregate_buffer_alloc_counted_mem_any_block >> simp[]
QED

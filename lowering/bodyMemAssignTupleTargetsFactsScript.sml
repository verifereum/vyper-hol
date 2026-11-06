(* Memory-boundary probes for tuple assignment.  In particular these do not
   require a newly executed ALLOCA to increase the allocation frontier. *)
Theory bodyMemAssignTupleTargetsFacts
Ancestors
  bodySimStmtCases bodyMemAssignTupleLocalsPrep bodyDeclMemoryCounted tupleTypedLoad instMemFrontier
  exprLoweringProps venomMemDefs compileEnv tupleMemoryLayout valueEncodingProofs
  context venomInst bodyDeclMemoryCore exprSimAlloc exprSimBufferStore
  venomExecSemantics venomState loweringSlice loweringPosts list
  fragExec fragExecMem bodyMemoryDefs bodyExprPreFacts bodySim
  tupleTargetStoreProps memoryLocalRhsProps allocLimitsProps allocLimits
  supportedStmtTraverse supportedStmts exprSimHyps exprSimAggregateLayout
  exprSimTopLevelProps exprSimFieldLayout exprSimAttributeFields
  accountsRelProps vyperStorageLayoutSafety vyperPlaceResultTyping
  vyperTypeEnv vyperLookupStorage vyperTypeSystem vyperTypeCallGraph gasContext
  vyperTypeCallStackSoundness exprSimHypsDefs exprSimSource
  vyperTypeInvariants stmtSimAugAssign stmtSimDeclStore
  bodyStorageMetadata stmtSimAssignAttr supportedExprForms supportedExprs
  exprSimUnwrap supportedTypes vyperLookup vyperState
Libs
  monadsyntax

(* Strengthen the existing tuple_container_bound interface from word-address
   representability to the actual memory-check frontier. *)
Theorem tuple_container_frontier:
  !ctx func cenv cx es s b sz.
    stmt_state_rel ctx func cenv cx es s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) ==>
    b + sz <= s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      metis_tac[]) >>
  fs[local_region_def, stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

(* All loads, not just the bytes occupied by the current value, fit. *)
Theorem tuple_element_frontier:
  !tvs i base s.
    i < LENGTH tvs /\
    base + type_memory_size_list tvs <= s.vs_alloca_next ==>
    base + SUM (MAP type_memory_size (TAKE i tvs)) +
      type_memory_size (EL i tvs) <= s.vs_alloca_next
Proof
  rpt strip_tac >> drule tuple_element_interval >>
  fs[type_memory_size_list_sum] >> decide_tac
QED

(* Provenance is retained across the copy, even when the ALLOCA is reused.
   Room alone is not used to infer the existence of a backing allocation. *)
Theorem tuple_scratch_prefix_provenance:
  !ctx func ce cx es s sa sm sn buf src n sw a t.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
    fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    run_inst_seq (emitted_insts sa sm) s = OK a /\
    run_inst_seq (emitted_insts sm sn) a = OK t ==>
    ?w. eval_operand buf.buf_operand t = SOME w /\
        FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  `a.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `n < dimword (:256)` by decide_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >> gvs[] >>
  qexists_tac `w` >> Cases_on `n = 0` >>
  gvs[mcopy_def, write_memory_with_expansion_def, eval_operand_def,
      lookup_var_def]
QED

Theorem tuple_scratch_prefix_path_mem:
  !ctx func ce cx es s sa sm sn buf src n sw tv v d.
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
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  drule_all tuple_scratch_prefix_provenance >> strip_tac >> gvs[] >>
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
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sn.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >>
  Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]
QED

(* This is the actual emitted tuple snapshot, not an uncounted S1 run.
   There is intentionally no premise that the allocation site is new. *)
Theorem tuple_stage_copy_path_mem:
  !ctx func ce cx es s sa sb staged src n sw tv v d.
    (do buf <- compile_alloc_buffer n;
        emit_void MCOPY [buf.buf_operand; src; Lit (n2w n)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    0 < n /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
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
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ sa = (staged,sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer n sa = (buf,sm)` >>
  rename1 `fn_has_code sa sb func` >>
  `compile_copy_memory buf.buf_operand src n sm = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  `w2n sw + n <= s.vs_alloca_next` by decide_tac >>
  drule_all tuple_scratch_prefix_path_mem >>
  strip_tac >> qexistsl_tac [`t`, `w`] >> simp[]
QED


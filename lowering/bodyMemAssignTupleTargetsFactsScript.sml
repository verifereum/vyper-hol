(* Memory-boundary probes for tuple assignment.  In particular these do not
   require a newly executed ALLOCA to increase the allocation frontier. *)
Theory bodyMemAssignTupleTargetsFacts
Ancestors
  bodyDeclMemoryCounted tupleTypedLoad instMemFrontier
  exprLoweringProps venomMemDefs compileEnv tupleMemoryLayout valueEncodingProofs
  context venomInst
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
      w2n w + n <= t.vs_alloca_next
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
  drule_all compile_scratch_prefix_body_path >>
  strip_tac >> qexistsl_tac [`t`, `w`] >> simp[]
QED

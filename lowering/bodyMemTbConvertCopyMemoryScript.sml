(* Allocation followed by a whole-buffer copy, as used by convert. *)
Theory bodyMemTbConvertCopyMemory
Ancestors bodyAllocMemory bodyCopyMemory exprLowering
  emitHelper
  exprOpenPrimitives exprSimDefs exprSimAlloc fragExecMem
  exprLoweringProps compileEnv context emitHelperProps fragExec venomMemDefs
  words finite_map arithmetic venomState

Theorem convert_widen_copy_frag_mem:
  compile_bytestring_widen_copy d x k sa = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated sa /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME p /\ w2n p + k <= s.vs_alloca_next /\
  alloca_history func s /\ val_in_memory tv v (w2n p) s.vs_memory /\
  val_wf tv v /\ val_footprint tv v <= k ==>
  frag_exec_mem ctx sa sb (\z. z = s)
    (\t. ?w. eval_operand op t = SOME w /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      w2n w + d <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,d) /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
        FLOOKUP t.vs_allocas aid = SOME a)) R
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_widen_copy _ _ _ _ = _` mp_tac >>
  simp[compile_bytestring_widen_copy_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer d sa = (buf,mid)` >>
  rename1 `compile_copy_memory buf.buf_operand x k mid = ((),sb)` >>
  `ci_mono sa mid /\ ci_mono mid sb` by
    (qspecl_then [`d`, `sa`] mp_tac ci_mono_compile_alloc_buffer >>
     qspecl_then [`buf.buf_operand`, `x`, `k`, `mid`] mp_tac
       ci_mono_compile_copy_memory >> simp[]) >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  drule_all alloc_buffer_source_frag_mem >>
  disch_then (qspec_then `R` strip_assume_tac) >> gvs[] >>
  `w2n w + d <= u.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> simp[]) >>
  `~block_is_terminated mid` by metis_tac[compile_alloc_buffer_open] >>
  `k < dimword (:256) /\ w2n p + k <= u.vs_alloca_next /\
   w2n w + k <= u.vs_alloca_next` by decide_tac >>
  drule_all compile_copy_memory_body_frag_mem >>
  disch_then (qspecl_then [`p`, `v`, `tv`, `u`, `w`, `ctx`, `R`] assume_tac) >>
  irule frag_exec_mem_seq >>
  qexistsl [`(\z. z = u /\ alloca_history func z)`, `mid`] >>
  `cs_extends sa mid /\ cs_extends mid sb` by fs[ci_mono_def] >>
  simp[] >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- fs[stmt_state_rel_def, ADD_COMM] >>
  rpt strip_tac >> fs[eval_operand_def, lookup_var_def, ADD_COMM]
QED

(* The memory-return INVOKE endpoint retains the caller's return-buffer
   owner. Typed bytes come from the callee exit, not from a memory frame. *)
Theory tupleAssignImmutableDeployIntMemoryOwned
Ancestors
  intCallFrame bodyIntCallSeams exprSimCopy venomState venomExecSemantics

Theorem tuple_immutable_memory_return_owned:
  bind_outputs outs vals (adopt_return_fmp ir (merge_callee_state t cs')) = SOME u /\
  intcall_callee_exit func ce cx rtv 0 (SOME w) n t (INL v) ee (IntRet ir cs') /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!name lb lsz. local_region ce scopes t name lb lsz ==>
    w2n w + sz <= lb \/ lb + lsz <= w2n w) ==>
  eval_operand p.ptr_operand u = SOME w /\ p.ptr_location = LocMemory /\
  FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  val_in_memory rtv v (w2n w) u.vs_memory /\
  (!name lb lsz. local_region ce scopes u name lb lsz ==>
    w2n w + sz <= lb \/ lb + lsz <= w2n w)
Proof
  strip_tac >>
  drule invoke_return_frame >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by
    metis_tac[] >>
  `u.vs_labels = t.vs_labels` by
    (qspecl_then [`ZIP (outs, vals)`,
       `adopt_return_fmp ir (merge_callee_state t cs')`]
       strip_assume_tac foldl_update_var_frame >>
     `?vars. u = (adopt_return_fmp ir (merge_callee_state t cs'))
                     with vs_vars := vars` by
       (fs[bind_outputs_def] >> metis_tac[]) >>
     pop_assum strip_assume_tac >>
     Cases_on `ir.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def]) >>
  `val_in_memory rtv v (w2n w) u.vs_memory` by
    gvs[intcall_callee_exit_def] >>
  simp[] >> rpt strip_tac >>
  `local_region ce scopes t name lb lsz` by
    (drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

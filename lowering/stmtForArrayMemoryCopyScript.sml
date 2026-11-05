(* Memory access certificates for array element copies. *)
Theory stmtForArrayMemoryCopy
Ancestors
  stmtSimForArray bodyDeclMemoryCore allocaFootprint fragExecMem
  stmtLowering emitHelper emitHelperProps exprLoweringProps
  venomState venomExecSemantics compileEnv list instMemFrontier stmtSimReturn valueTypingMemoryProps exprSimProps

Theorem array_iter_word_copy_mem_ok:
  is_word_type ty /\
  compile_iter_elem_copy ce src dst bytes LocMemory F ty ty sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  `!w. eval_operand dst
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) = SOME dw` by
    (Cases_on `dst` >>
     gvs[eval_operand_def, lookup_var_update_var, not_fresh_at_def]) >>
  gvs[compile_iter_elem_copy_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      comp_return_def, LET_THM] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_cons,
       run_inst_seq_mem_ok_last] >>
  qpat_assum `eval_operand src s = SOME sw`
    (mp_then Any assume_tac step_MLOAD) >>
  simp[below_frontier_MLOAD, below_frontier_MSTORE] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!w. eval_operand dst (update_var _ w s) = _`
    (qspec_then `mload (w2n sw) s` mp_tac) >>
  simp[update_var_def]
QED

Theorem array_iter_copy_mem_ok:
  compile_iter_elem_copy ce src dst bytes LocMemory F ty ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> Cases_on `is_word_type ty`
  >- (drule_all word_type_sizes >> strip_tac >>
      irule array_iter_word_copy_mem_ok >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[compile_iter_elem_copy_def] >>
  drule val_store_size_le >> strip_tac >>
  irule body_typed_store_memory_mem_ok >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  goal_assum (drule_at (Pat `eval_operand dst s = _`)) >>
  simp[] >- first_assum ACCEPT_TAC >> decide_tac
QED

(* Pointer interfaces for raw_revert. *)
Theory rawRevertPtrBoundary
Ancestors
  exprSimRawRevertCore exprSimHypsDefs vyperTypeSystem vyperAST
  list bodyPtrDefs ptrSafeRun ptrDiscipline venomInst venomState
  venomExecSemantics contextCodegenRel codegenRel memLocDefs
  stmtReasonMemory fragGasPathPtr gasCount fragExec

Theorem raw_revert_pre_bytes:
  expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
  ?e cap. args = [e] /\ expr_body_pre cenv cx env e es /\
    expr_type e = BaseT (BytesT (Dynamic cap))
Proof
  strip_tac >> drule raw_revert_pre_arg >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` mp_tac >>
  simp[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]
QED

Theorem ptr_inst_ok_revert:
  eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
  FLOOKUP G p = SOME (b,sz) /\ b <= w2n w /\
  w2n w + w2n n <= b + sz /\
  op_taint tn (Var p) = {} /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id REVERT [Var p;len] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, step_inst_non_invoke, step_revert_eq,
       mk_inst_def, allocas_from_def] >>
  simp[access_ok_def, taint_ok_def, about_to_revert_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mem_read_ops_def, mk_inst_def] >>
  metis_tac[]
QED

Theorem revert_counted_edge_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id REVERT [Var p;len] []) /\
  eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
  FLOOKUP G p = SOME (b,sz) /\ b <= w2n w /\
  w2n w + w2n n <= b + sz /\
  op_taint tn (Var p) = {} /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx ==>
  ?t. gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (Abort Revert_abort t)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id REVERT [Var p;len] []) s` by
    (irule ptr_inst_ok_revert >> metis_tac[]) >>
  simp[gas_path_ptr_edge_def] >>
  qrefinel [`_`, `0`] >>
  simp[step_inst_non_invoke, step_revert_eq, gas_count_step_def,
       ptr_safe_step_def, mk_inst_def, exit_result_def] >>
  metis_tac[]
QED

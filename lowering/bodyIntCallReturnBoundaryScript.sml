(* Diagnostics of the universal statement-return boundary.  These do not
   assert a counterexample to the packaged-callee seam. *)
Theory bodyIntCallReturnBoundary
Ancestors
  bodySim stmtSimDefs loweringPosts exprLoweringProps compileEnv
  venomState venomMemDefs words finite_map

Theorem ret_pc_ok_return_buf_independent:
  ret_pc_ok (cenv with ce_return_buf := rb) sa s = ret_pc_ok cenv sa s
Proof
  simp[ret_pc_ok_def]
QED

Theorem local_ptrs_reserved_return_buf_independent:
  local_ptrs_reserved (cenv with ce_return_buf := rb) sa =
  local_ptrs_reserved cenv sa
Proof
  simp[local_ptrs_reserved_def]
QED

Theorem ret_pc_ok_undefined_return_buffer[local]:
  let ce = cenv with <|ce_return_pc := NONE;
                       ce_return_buf := SOME (PtrVar (Var x) 32)|> in
  let t = s with vs_vars := FEMPTY in
    ret_pc_ok ce sa t /\ eval_operand (Var x) t = NONE /\
    ~(?bw cap. return_buf_frame (SOME (bw,cap)) ce sa t)
Proof
  simp[ret_pc_ok_def, return_buf_frame_def, eval_operand_def, lookup_var_def]
QED

Theorem stmt_state_rel_return_buf_independent:
  stmt_state_rel ctx func (cenv with ce_return_buf := rb) cx es s =
  stmt_state_rel ctx func cenv cx es s
Proof
  `log_entry_equiv (cenv with ce_return_buf := rb) cx.txn.target =
   log_entry_equiv cenv cx.txn.target` by
    simp[FUN_EQ_THM, log_entry_equiv_def] >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, storage_vars_rel_def, transient_vars_rel_def,
       immutables_rel_def, logs_rel_def, immutable_alloca_sep_def,
       immutable_base_zero_def, log_entry_equiv_def]
QED


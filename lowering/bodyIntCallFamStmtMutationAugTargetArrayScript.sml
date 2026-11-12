(* Bounds/pointer suffix at the actual state, without a freshness premise. *)
Theory bodyIntCallFamStmtMutationAugTargetArray
Ancestors
  bodyIntCallFamStmtMutationBinop bodyIntCallJointContract
  exprSimSubscriptArrayFramed exprSimArrayIndex fragGasFresh freshWrites
  varsExt exprLoweringProps compileEnv loweringStateRelDefs

Theorem intcall_array_check_ptr_path:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  comp_ignore_bind (array_bounds_check idx len sgn)
    (array_elem_ptr base_op idx dyn ws esz) sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\
  eval_operand base_op s = SOME b /\ eval_operand idx s = SOME i /\
  eval_operand len s = SOME n /\
  (!x. base_op = Var x \/ idx = Var x \/ len = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ idx_in_range sgn i n ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sb u /\
      eval_operand op u = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  strip_tac >>
  `local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx (drop_fresh sa s) = SOME i /\
   eval_operand len (drop_fresh sa s) = SOME n` by
    metis_tac[eval_operand_drop_fresh] >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
    eval_operand op t0 = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)` by
    (irule array_check_ptr_run >> metis_tac[fresh_vars_wrt_drop_fresh]) >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx len sgn)
    (array_elem_ptr base_op idx dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  irule intcall_expr_cont_readonly_path >> simp[] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[straight_fresh_def] >>
  metis_tac[local_ptrs_reserved_next_var]
QED

Theorem intcall_array_check_ptr_oob_path:
  comp_ignore_bind (array_bounds_check idx len sgn)
    (array_elem_ptr base_op idx dyn ws esz) sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  (!x. idx = Var x \/ len = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~idx_in_range sgn i n ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (Abort Revert_abort u)
Proof
  strip_tac >>
  `eval_operand idx (drop_fresh sa s) = SOME i /\
   eval_operand len (drop_fresh sa s) = SOME n` by
    metis_tac[eval_operand_drop_fresh] >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) =
      Abort Revert_abort t0` by
    (irule array_check_ptr_oob >> metis_tac[fresh_vars_wrt_drop_fresh]) >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx len sgn)
    (array_elem_ptr base_op idx dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  metis_tac[]
QED

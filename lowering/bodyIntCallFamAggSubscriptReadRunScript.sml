(* Arithmetic and hashing resources at supplied raw endpoints. *)
Theory bodyIntCallFamAggSubscriptReadRun
Ancestors
  bodyIntCallFamAggSubscriptReadOnly bodyIntCallJointContract
  exprSimMapKey exprSimHash emitHelperProps emitHelper compileEnv context
  venomState venomInst exprLoweringProps

Theorem intcall_add_run_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\
  emit_op ADD [lhs; rhs] si = (op,sb) /\
  eval_operand lhs s = SOME w0 /\ eval_operand rhs s = SOME w1 /\
  fn_has_code si sb fp.jc_func /\
  run_inst_seq (emitted_insts si sb) s = OK t ==>
  intcall_expr_cont fp ce env es0 sa s0 es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op t = SOME (w0 + w1) /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_ADD_frame >> strip_tac >> gvs[] >>
  irule (cj 2 intcall_readonly_run_landing) >> simp[] >>
  qexistsl_tac [`s`, `si`] >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[mk_inst_def, is_terminator_def] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def]
QED

Theorem intcall_sha3_run_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\
  emit_op SHA3 [ptr_op; len] si = (op,sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  fn_has_code si sb fp.jc_func /\
  run_inst_seq (emitted_insts si sb) s = OK t ==>
  intcall_expr_cont fp ce env es0 sa s0 es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at (w2n p) (w2n n) s.vs_memory =
   mem_bytes_at (w2n p) (w2n n) s.vs_memory` by simp[] >>
  drule_all emit_SHA3_bytes_frame >> strip_tac >> gvs[] >>
  irule (cj 2 intcall_readonly_run_landing) >> simp[] >>
  qexistsl_tac [`s`, `si`] >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[mk_inst_def, is_terminator_def] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def]
QED

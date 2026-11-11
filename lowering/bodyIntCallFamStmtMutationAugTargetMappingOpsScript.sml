(* Concrete readonly endpoints used inside the allocating mapping suffix. *)
Theory bodyIntCallFamStmtMutationAugTargetMappingOps
Ancestors
  bodyIntCallFamStmtMutationAugTargetMappingTail exprSimMapKey exprSimHash
  bodyIntCallJointContract venomInst venomState

Theorem intcall_mapping_add_run:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_op ADD [a;b] sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      intcall_expr_cont fp ce env es sa s es sb
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      eval_operand op t = SOME (x+y) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s)
Proof
  strip_tac >> drule_all emit_ADD_frame >> strip_tac >>
  qexists `t` >> simp[] >>
  irule intcall_readonly_emit_run >> simp[is_terminator_def] >>
  goal_assum (drule_at Any) >> simp[is_terminator_def]
QED

Theorem intcall_mapping_hash_run:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_op SHA3 [ptr_op;len] sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      intcall_expr_cont fp ce env es sa s es sb
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      eval_operand op t = SOME
        (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s)
Proof
  strip_tac >> drule_all emit_SHA3_bytes_frame >> strip_tac >>
  qexists `t` >> simp[] >>
  irule intcall_readonly_emit_run >> simp[is_terminator_def] >>
  goal_assum (drule_at Any) >> simp[is_terminator_def]
QED

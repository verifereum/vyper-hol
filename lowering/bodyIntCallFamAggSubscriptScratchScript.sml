(* Readonly arithmetic and counted mapping scratch construction. *)
Theory bodyIntCallFamAggSubscriptScratch
Ancestors
  bodyIntCallFamAggSubscriptStore bodyIntCallFamAggSubscriptReadOnly
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimMapKey
  emitHelperProps emitHelper context compileEnv exprLoweringProps
  venomState venomInst freshWrites

Theorem intcall_emit_add_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\
  emit_op ADD [lhs; rhs] si = (op,sb) /\
  eval_operand lhs s = SOME w0 /\ eval_operand rhs s = SOME w1 /\
  fn_has_code si sb fp.jc_func ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es0 sa s0 es sb u /\
      eval_operand op u = SOME (w0 + w1) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
      (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_ADD_frame >> strip_tac >>
  `sb.cs_current_bb = si.cs_current_bb` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   intcall_expr_cont fp ce env es0 sa s0 es sb
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule intcall_readonly_run_landing >> simp[] >>
     qexists_tac `si` >> simp[mk_inst_def, is_terminator_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, not_fresh_at_def] >>
  fs[venom_state_component_equality, not_fresh_at_def, lookup_var_def]
QED

Theorem intcall_emit_sha3_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\
  emit_op SHA3 [ptr_op; len] si = (op,sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  fn_has_code si sb fp.jc_func ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es0 sa s0 es sb u /\
      eval_operand op u = SOME
        (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
      (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exprSimHashTheory.emit_SHA3_bytes_frame >> strip_tac >>
  `sb.cs_current_bb = si.cs_current_bb` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   intcall_expr_cont fp ce env es0 sa s0 es sb
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule intcall_readonly_run_landing >> simp[] >>
     qexists_tac `si` >> simp[mk_inst_def, is_terminator_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, not_fresh_at_def] >>
  fs[venom_state_component_equality, not_fresh_at_def, lookup_var_def]
QED

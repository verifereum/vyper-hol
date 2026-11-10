(* Single readonly emissions preserve the internal-call continuation. *)
Theory bodyIntCallFamStmtMutationLoad
Ancestors
  bodyIntCallFamStmtMutationBinop emitHelperProps exprLoweringProps
  exprSimProps compileEnv emitHelper venomState venomInst fragGasMode
  loweringShapeRules bodyIntCallJointContract exprSimOperands finite_map

Theorem intcall_emit_readonly_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_op opc args sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
         OK (update_var out w s)) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      eval_operand op u = SOME w /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  drule_all emit_op_zero_path >>
  disch_then (qspec_then `fp.jc_ctx` assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  qexists `update_var q w s with vs_inst_idx := SUC s.vs_inst_idx` >>
  fs[gas_marked_path_def, eval_operand_def, lookup_var_def, update_var_def,
     FLOOKUP_UPDATE] >>
  `local_ptrs_reserved ce sa` by fs[intcall_expr_res_def] >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `not_local_ptr ce es.scopes q` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> metis_tac[]) >>
  irule intcall_expr_cont_readonly_path >>
  simp[update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> `x <> q` by metis_tac[] >>
      gvs[lookup_var_def, FLOOKUP_UPDATE]) >>
  reverse conj_tac
  >- (`stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es
         (update_var q w s with vs_inst_idx := SUC (LENGTH sa.cs_current_insts))`
        suffices_by simp[update_var_def] >>
      rewrite_tac[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> fs[intcall_expr_res_def]) >>
  qexistsl_tac [`F`, `0`] >> simp[gas_marked_path_def]
QED

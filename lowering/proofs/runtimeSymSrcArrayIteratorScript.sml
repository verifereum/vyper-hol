Theory runtimeSymSrcArrayIterator
Ancestors
  supportedStmts supportedExprs vyperAST list runtimeSymSrcInterfaces
  runtimeSymSrcEmission exprLowering context finite_map venomInst stackPlanTypes

Theorem runtime_sym_array_iterator_type:
  supported_iterator tops fty (Array e) n ==>
  ?bd. expr_type e = ArrayT fty bd /\ bound_length bd <= n
Proof
  Cases_on `e` >> simp[supported_iterator_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `b` >>
  gvs[bound_length_def] >> metis_tac[bound_length_def]
QED

Theorem runtime_sym_toplevel_name_eval:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce ty (TopLevelName rt ns) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  simp[Once compile_expr_def, compile_expr_body_def] >>
  Cases_on `FLOOKUP ce.ce_module_vars ns` >>
  simp[runtime_sym_value_def, mk_ptr_def, is_label_operand_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      simp[runtime_sym_inst_def, mk_inst_def, runtime_sym_value_def,
           is_label_operand_def]) >>
  Cases_on `x` >>
  simp[runtime_sym_value_def, mk_ptr_def, is_label_operand_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `emit_inst INVALID [] [] s` >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_inst_def, mk_inst_def, runtime_sym_value_def,
       is_label_operand_def]
QED

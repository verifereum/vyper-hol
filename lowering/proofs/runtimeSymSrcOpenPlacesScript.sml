Theory runtimeSymSrcOpenPlaces
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering compileEnv context list supportedExprs supportedExprTraverse
  finite_map venomInst loweringShapeDefs stackPlanTypes

Theorem runtime_sym_target_base:
  !target ce. runtime_sym_env ce ==>
  ~is_label_operand (compile_target_base ce target)
Proof
  gen_tac >> measureInduct_on `vyperAST$base_assignment_target_size target` >>
  Cases_on `target` >> simp[compile_target_base_def, vyperASTTheory.expr_size_def] >> rpt strip_tac
  >- (Cases_on `FLOOKUP ce.ce_vars s` >> gvs[is_label_operand_def] >>
      Cases_on `x` >> gvs[is_label_operand_def] >>
      drule_all runtime_sym_env_local >> simp[runtime_sym_loc_def]) >>
  Cases_on `FLOOKUP ce.ce_module_vars p` >> gvs[is_label_operand_def] >>
  Cases_on `x` >> gvs[is_label_operand_def]
QED

Theorem runtime_sym_attribute:
  runtime_sym_attribute_clause tops
Proof
  rewrite_tac[runtime_sym_attribute_clause_def] >>
  map_every qx_gen_tac [`cfn`,`ce`,`rt`,`ty`,`base_e`,`fld`,`s`,`v`,`s'`] >>
  strip_tac >>
  `supported_expr tops base_e \/ supported_place_expr tops base_e \/
   supported_effect_place_expr tops base_e` by
    (gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def]) >>
  `~supported_expr_exists is_self_code base_e` by
    gvs[supported_expr_exists_def] >>
  qpat_x_assum `compile_attribute _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_attribute_def, comp_bind_def] >>
  Cases_on `cfn ce ty base_e s` >> simp[] >>
  pairarg_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule runtime_sym_value_operand >> strip_tac >>
  drule_at (Pos last) runtime_sym_emit_op >> simp[is_label_operand_def] >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED

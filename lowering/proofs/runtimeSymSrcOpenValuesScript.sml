Theory runtimeSymSrcOpenValues
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission
  runtimeSymSrcInterfaces exprLowering compileEnv list supportedExprTraverse

Theorem runtime_sym_lower_value:
  (!ce v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
     EVERY runtime_sym_inst (state_insts s) /\
     unwrap_value ce v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_lower_value_clause tops
Proof
  rw[runtime_sym_lower_value_clause_def, lower_value_def, comp_bind_def] >>
  Cases_on `cfn ce ty e s` >> gvs[] >>
  fs[runtime_sym_expr_contract_def] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_lower_value_with_loc:
  (!ce v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
     EVERY runtime_sym_inst (state_insts s) /\
     unwrap_value ce v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_lower_value_with_loc_clause tops
Proof
  rw[runtime_sym_lower_value_with_loc_clause_def,
     lower_value_with_loc_def, comp_bind_def, comp_return_def] >>
  Cases_on `cfn ce ty e s` >> gvs[] >>
  Cases_on `unwrap_value ce q r` >> gvs[] >>
  fs[runtime_sym_expr_contract_def] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_multi_vvs:
  runtime_sym_multi_vvs_clause tops
Proof
  rewrite_tac[runtime_sym_multi_vvs_clause_def] >>
  gen_tac >> gen_tac >> Induct >>
  simp[compile_multi_vvs_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[comp_bind_def] >>
  Cases_on `cfn ce (expr_type h) h s` >> gvs[] >>
  Cases_on `compile_multi_vvs cfn ce es r` >> gvs[] >>
  gvs[comp_return_def] >>
  qpat_x_assum `~supported_exprs_exists _ (h::es)` mp_tac >>
  simp[supported_exprs_exists_every] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (expr_type h) h` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops h` by
    metis_tac[runtime_sym_supported_argument, MEM, EVERY_DEF] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `~supported_exprs_exists is_self_code es` by
    simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  first_x_assum drule_all >> simp[]
QED

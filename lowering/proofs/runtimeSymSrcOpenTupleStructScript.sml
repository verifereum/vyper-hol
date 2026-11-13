Theory runtimeSymSrcOpenTupleStruct
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission
  runtimeSymSrcInterfaces exprLowering compileEnv list supportedExprTraverse
  context emitHelper venomInst stackPlanTypes

Theorem runtime_sym_make_tuple:
  (!ce vv s v s'. runtime_sym_env ce /\ runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\
    unwrap_value ce vv s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!ce v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_make_tuple_clause tops
Proof
  rewrite_tac[runtime_sym_make_tuple_clause_def] >>
  strip_tac >> gen_tac >> gen_tac >> Induct >-
    simp[compile_make_tuple_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `~supported_exprs_exists _ (h::es)` mp_tac >>
  simp[supported_exprs_exists_every, NoAsms] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (expr_type h) h` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops h` by
    metis_tac[runtime_sym_supported_argument, MEM, EVERY_DEF] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >> strip_tac >>
  `!e ty. MEM e es ==> runtime_sym_expr_contract tops cfn ce ty e` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!e ty. MEM e (h::es) ==> _` kall_tac >>
  qpat_x_assum `compile_make_tuple _ _ (h::es) _ _ _ = _` mp_tac >>
  simp[Once compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def, NoAsms] >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts cs') /\ runtime_sym_value vv` by
    (first_x_assum irule >> metis_tac[]) >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts cs'') /\ ~is_label_operand dst` by
    (irule runtime_sym_emit_op >>
     goal_assum (drule_at Any) >>
     simp[is_label_operand_def, NoAsms] >> asm_rewrite_tac[]) >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts cs''') /\ ~is_label_operand v` by
    (first_x_assum drule_all >> simp[]) >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs'''')` by
    (first_x_assum drule_all >> simp[]) >>
  `~supported_exprs_exists is_self_code es` by
    simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  first_x_assum irule >>
  asm_rewrite_tac[] >> simp[EVERY_DEF, NoAsms] >>
  conj_tac >- (qpat_x_assum `EVERY _ (h::es)` mp_tac >> simp[EVERY_DEF, NoAsms]) >>
  qexistsl [`buf`, `off + type_memory_bytes ce (expr_type h)`, `cs''''`] >>
  asm_rewrite_tac[]
QED

Theorem runtime_sym_struct_lit:
  (!ce vv s v s'. runtime_sym_env ce /\ runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\
    unwrap_value ce vv s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!ce v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_struct_lit_clause tops
Proof
  rewrite_tac[runtime_sym_struct_lit_clause_def] >>
  strip_tac >> gen_tac >> gen_tac >> gen_tac >> Induct >-
    simp[compile_struct_lit_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `~supported_fields_exists _ _` mp_tac >>
  simp[supported_fields_exists_every, NoAsms] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (expr_type h1) h1` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops h1` by
    (irule runtime_sym_supported_argument >> qexists_tac `[h1]` >>
     qpat_x_assum `EVERY _ ((h0,h1)::fields)` mp_tac >>
     simp[EVERY_DEF, NoAsms]) >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >> strip_tac >>
  `!e t. MEM e (MAP SND fields) ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!e t. MEM e (MAP SND ((h0,h1)::fields)) ==> _` kall_tac >>
  qpat_x_assum `compile_struct_lit _ _ _ ((h0,h1)::fields) _ _ _ = _` mp_tac >>
  simp[Once compile_struct_lit_def, comp_bind_def, comp_ignore_bind_def, NoAsms] >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts cs') /\ runtime_sym_value vv` by
    (first_x_assum irule >> metis_tac[]) >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts cs'') /\ ~is_label_operand dst` by
    (irule runtime_sym_emit_op >> goal_assum (drule_at Any) >>
     simp[is_label_operand_def, NoAsms] >> asm_rewrite_tac[]) >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts cs''') /\ ~is_label_operand v` by
    (first_x_assum drule_all >> simp[]) >>
  pairarg_tac >> asm_rewrite_tac[] >> simp[NoAsms] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs'''')` by
    (first_x_assum drule_all >> simp[]) >>
  `~supported_fields_exists is_self_code fields` by
    simp[supported_fields_exists_every, GSYM EVERY_NOT_EXISTS] >>
  `EVERY (supported_pure_expr tops o SND) fields` by
    (qpat_x_assum `EVERY _ ((h0,h1)::fields)` mp_tac >>
     simp[EVERY_DEF, NoAsms]) >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  qexists_tac `buf` >> asm_rewrite_tac[] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  goal_assum (drule_at Any)
QED

Theory runtimeSymSrcOpenLists
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission
  runtimeSymSrcInterfaces exprLowering compileEnv list supportedExprTraverse
  stackPlanTypes

Theorem runtime_sym_multi_exprs:
  runtime_sym_lower_value_clause tops ==>
  runtime_sym_multi_exprs_clause tops
Proof
  rewrite_tac[runtime_sym_lower_value_clause_def,
              runtime_sym_multi_exprs_clause_def] >>
  strip_tac >> gen_tac >> gen_tac >> Induct >>
  simp[compile_multi_exprs_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[comp_bind_def] >>
  Cases_on `lower_value cfn ce (expr_type h) h s` >> gvs[] >>
  Cases_on `compile_multi_exprs cfn ce es r` >>
  gvs[comp_return_def] >>
  qpat_x_assum `~supported_exprs_exists _ (h::es)` mp_tac >>
  simp[supported_exprs_exists_every] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (expr_type h) h` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops h` by
    metis_tac[runtime_sym_supported_argument, MEM, EVERY_DEF] >>
  `EVERY runtime_sym_inst (state_insts r) /\ ~is_label_operand q` by
    (first_x_assum irule >> metis_tac[]) >>
  `~supported_exprs_exists is_self_code es` by
    simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_abi_encode_args:
  (!ce vv s op s'. runtime_sym_env ce /\ runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\
    unwrap_value ce vv s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce ty vv s op s'. runtime_sym_env ce /\ runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_materialize_vv ce ty vv s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_abi_encode_args_clause tops
Proof
  rewrite_tac[runtime_sym_abi_encode_args_clause_def] >>
  strip_tac >> gen_tac >> gen_tac >> Induct >>
  simp[compile_abi_encode_args_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> gvs[comp_bind_def] >>
  Cases_on `cfn ce (expr_type h) h s` >> gvs[] >>
  qpat_x_assum `~supported_exprs_exists _ (h::es)` mp_tac >>
  simp[supported_exprs_exists_every] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (expr_type h) h` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops h` by
    metis_tac[runtime_sym_supported_argument, MEM, EVERY_DEF] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >>
  simp[] >> disch_then drule_all >> strip_tac >>
  Cases_on `~is_word_type (expr_type h) /\ exprs_can_mutate ce es` >>
  gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[comp_return_def] >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand op` by
    (first_x_assum drule_all >> simp[]) >>
  `~supported_exprs_exists is_self_code es` by
    simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_concat:
  runtime_sym_lower_value_clause tops ==> runtime_sym_concat_clause tops
Proof
  rewrite_tac[runtime_sym_lower_value_clause_def, runtime_sym_concat_clause_def] >>
  strip_tac >> gen_tac >> gen_tac >> Induct >-
    simp[compile_concat_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `infos` >- gvs[compile_concat_def, comp_return_def] >>
  PairCases_on `h'` >>
  qpat_x_assum `~supported_exprs_exists _ (h::es)` mp_tac >>
  simp[supported_exprs_exists_every] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (expr_type h) h` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops h` by
    metis_tac[runtime_sym_supported_argument, MEM, EVERY_DEF] >>
  `~supported_exprs_exists is_self_code es` by
    simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  Cases_on `h'0` >>
  qpat_x_assum `compile_concat _ _ (h::es) _ _ _ _ = _` mp_tac >>
  simp[Once compile_concat_def, comp_bind_def, comp_ignore_bind_def, NoAsms] >>
  Cases_on `lower_value cfn ce (expr_type h) h s` >>
  simp[NoAsms] >>
  `EVERY runtime_sym_inst (state_insts r) /\ ~is_label_operand q` by
    (first_x_assum irule >> metis_tac[])
  >- suspend "bytes"
  >> suspend "word"
QED

Resume runtime_sym_concat[bytes]:
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `emit_op MLOAD [q] r = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_op ADD [q; _] _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_op MLOAD [off] _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_op ADD [dst; _] _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_void MCOPY _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[MEM, EVERY_DEF]
QED

Resume runtime_sym_concat[word]:
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_op ADD [dst; _] _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_void MSTORE [_; q] _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[MEM, EVERY_DEF]
QED

Finalise runtime_sym_concat

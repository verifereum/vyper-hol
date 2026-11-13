Theory runtimeSymSrcTypeBuiltinBody
Ancestors
  runtimeSymSrcInterfaces stackPlanTypes
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission exprCallBounds
  supportedExprTraverse supportedExprForms supportedExprs exprLowering
  context compileEnv venomInst memoryValueDefs typedCopyDomain list memLocDefs
  builtinMisc builtinBytes builtinSimple

Theorem runtime_sym_type_builtin_body:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_type_builtin_contract tops
    (compile_type_builtin_dispatch_body cfn) ce vt ty tb rt args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_type_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_type_builtin_domain, supported_expr_exists_def] >>
  `!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[expr_list_member_bound]) >>
  Cases_on `tb`
  >~ [`Convert`] >- suspend "convert"
  >~ [`Empty`] >- suspend "empty"
  >~ [`Extract32`] >- gvs[runtime_sym_type_builtin_domain, runtime_sym_extract32_rejected]
  >~ [`AbiEncode ensure mid`] >- suspend "encode"
  >~ [`AbiDecode unwrap`] >- suspend "decode"
  >> gvs[compile_type_builtin_dispatch_body_def, AllCaseEqs(),
         runtime_sym_value_def, is_label_operand_def] >>
  pairarg_tac >> gvs[runtime_sym_value_def, is_label_operand_def]
QED

Resume runtime_sym_type_builtin_body[empty]:
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 5 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_type_builtin_dispatch_body_def] >>
  Cases_on `is_word_type rt` >> simp[]
  >- (strip_tac >> gvs[runtime_sym_value_def, is_label_operand_def]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def, base_ptr_def]
QED

Resume runtime_sym_type_builtin_body[convert]:
  `MEM (HD args) args /\ supported_expr tops (HD args)` by
    metis_tac[runtime_sym_convert_selection] >>
  `~supported_expr_exists is_self_code (HD args)` by
    gvs[supported_exprs_exists_every, EVERY_MEM] >>
  drule runtime_sym_generators_lower_value >>
  simp[runtime_sym_lower_value_clause_def] >> strip_tac >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 6 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_type_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand v'` by
    (first_x_assum (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >> simp[]) >>
  qpat_x_assum `!cfn ce ty e s op s'. _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_x_assum `!e t. MEM e args ==> _` kall_tac >>
  qpat_x_assum `runtime_sym_generator_contracts _` kall_tac >>
  qpat_x_assum `COND _ _ _ = _` mp_tac >>
  IF_CASES_TAC >> simp[]
  >- (disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
      simp[runtime_sym_value_def, is_label_operand_def]) >>
  IF_CASES_TAC >> simp[]
  >- (Cases_on `compile_bytestring_widen_copy (type_memory_bytes ce rt) v'
          (type_memory_bytes ce (lowered_value_type ce (HD args))) st1` >>
      simp[as_stack_val_def] >>
      strip_tac >> gvs[] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      simp[runtime_sym_value_def]) >>
  Cases_on `rt` >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt cv` >>
  Cases_on `cv` >> simp[as_stack_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def, is_label_operand_def]
QED
Resume runtime_sym_type_builtin_body[encode]:
  `?e bytes. args = [e] /\ ~ensure /\ mid = SOME bytes` by
    (Cases_on `args` >> gvs[runtime_sym_type_builtin_domain, supported_type_builtin_form_def] >>
     Cases_on `t` >> Cases_on `ensure` >> Cases_on `mid` >>
     gvs[runtime_sym_type_builtin_domain, supported_type_builtin_form_def]) >>
  gvs[] >>
  drule runtime_sym_generators_context >>
  disch_then (strip_assume_tac o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_abi >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_abi_clauses_def]) >>
  `runtime_sym_expr_contract tops cfn ce (expr_type e) e` by simp[] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  disch_then (assume_tac o SRULE [runtime_sym_expr_contract_def]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_type_builtin_dispatch_body_def] >>
  IF_CASES_TAC >> pure_asm_rewrite_tac[]
  >- suspend "encode_word"
  >> suspend "encode_memory"
QED

Resume runtime_sym_type_builtin_body[encode_word]:
  `supported_expr tops e` by
    (qpat_assum `supported_pure_expr tops e` mp_tac >>
     simp[NoAsms, supported_expr_def]) >>
  `~supported_expr_exists is_self_code e` by
    (qpat_assum `~supported_exprs_exists is_self_code [e]` mp_tac >>
     simp[NoAsms, supported_exprs_exists_every]) >>
  `runtime_sym_expr_contract tops cfn ce (expr_type e) e` by
    (first_x_assum irule >> simp[]) >>
  drule runtime_sym_generators_lower_value >>
  disch_then (assume_tac o SRULE [runtime_sym_lower_value_clause_def]) >>
  pairarg_tac >> first_assum (fn th => simp[NoAsms, th]) >>
  pairarg_tac >> first_assum (fn th => simp[NoAsms, th]) >>
  pairarg_tac >> first_assum (fn th => simp[NoAsms, th]) >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory encoded_pair` >>
  Cases_on `encoded_pair` >> simp[NoAsms, as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `!e' t. expr_size e' < _ ==> _` kall_tac >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand v'` by
    (first_x_assum (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `EVERY runtime_sym_inst (state_insts st3)` by
    (irule runtime_sym_emit_void >> goal_assum (drule_at Any) >>
     qexistsl [`MSTORE`, `[tmp_alloc.buf_operand; v']`, `_2`] >>
     Cases_on `_2` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[NoAsms, runtime_sym_value_def, mk_ptr_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Resume runtime_sym_type_builtin_body[encode_memory]:
  `supported_expr tops e` by
    (qpat_assum `supported_pure_expr tops e` mp_tac >>
     simp[NoAsms, supported_expr_def]) >>
  `~supported_expr_exists is_self_code e` by
    (qpat_assum `~supported_exprs_exists is_self_code [e]` mp_tac >>
     simp[NoAsms, supported_exprs_exists_every]) >>
  pairarg_tac >> first_assum (fn th => simp[NoAsms, th]) >>
  pairarg_tac >> first_assum (fn th => simp[NoAsms, th]) >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory encoded_pair` >>
  Cases_on `encoded_pair` >> simp[NoAsms, as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value src_vv` by
    (first_x_assum (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >>
     simp[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_type_builtin_body[decode]:
  `?e. args = [e] /\ ~unwrap` by
    (Cases_on `args` >> gvs[runtime_sym_type_builtin_domain, supported_type_builtin_form_def] >>
     Cases_on `t` >> Cases_on `unwrap` >>
     gvs[runtime_sym_type_builtin_domain, supported_type_builtin_form_def]) >>
  gvs[] >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_abi >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_abi_clauses_def]) >>
  `runtime_sym_expr_contract tops cfn ce (expr_type e) e` by simp[] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  disch_then (assume_tac o SRULE [runtime_sym_expr_contract_def]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_type_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory decoded_pair` >>
  Cases_on `decoded_pair` >> simp[as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value data_vv` by
    (first_x_assum (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >>
     simp[] >> gvs[supported_exprs_exists_every, supported_expr_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Finalise runtime_sym_type_builtin_body

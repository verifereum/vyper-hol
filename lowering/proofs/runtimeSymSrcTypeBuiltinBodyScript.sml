Theory runtimeSymSrcTypeBuiltinBody
Ancestors
  listZipProps
  runtimeSymSrcInterfaces stackPlanTypes
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission exprCallBounds
  supportedExprTraverse supportedExprForms supportedExprs exprLowering
  context compileEnv venomInst memoryValueDefs typedCopyDomain list memLocDefs
  exprLoweringProps
  builtinMisc builtinBytes builtinSimple emitHelper loweringShapeDefs
  runtimeSymSrcBuiltinByteSimple runtimeSymSrcBuiltinData runtimeSymSrcBinops
  runtimeSymSrcContextComplete runtimeSymSrcAbiEncode runtimeSymSrcExternalPrimitive

Theorem runtime_sym_extract32_clamp[local]:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_clamp_basetype v ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, comp_return_def] >>
  TRY (rename1 `compile_clamp_basetype v (BaseT bt) s` >>
       Cases_on `bt` >> simp[compile_clamp_basetype_def, comp_return_def]) >>
  TRY (rename1 `compile_clamp_basetype v (BaseT (BytesT bs)) s` >>
       Cases_on `bs` >> simp[compile_clamp_basetype_def, comp_return_def]) >>
  rpt IF_CASES_TAC >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  TRY (drule_all runtime_sym_clamp_and_return >> simp[] >> NO_TAC) >>
  ntac 2 (rev_dxrule runtime_sym_emit_op_result >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_emit_void_result >> simp[]
QED

Theorem runtime_sym_abi_encode_payload[local]:
  runtime_sym_env tops ce /\ EVERY runtime_sym_value vs /\
  (single ==> vs <> []) /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_payload ce single vs tys dst s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `single` >> simp[compile_abi_encode_payload_def]
  >- (Cases_on `vs` >> simp[comp_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      drule_all runtime_sym_unwrap_value >> strip_tac >>
      Cases_on `is_word_type (HD tys)` >> gvs[comp_ignore_bind_def, comp_bind_def,
        comp_return_def]
      >- (pairarg_tac >> gvs[] >>
          drule runtime_sym_emit_void_result >> simp[is_label_operand_def]) >>
      metis_tac[runtime_sym_abi_encode_to_buf]) >>
  strip_tac >>
  irule (MP_CANON runtime_sym_abi_encode_values_to_buf) >>
  conj_tac >- metis_tac[runtime_sym_abi_encode_to_buf] >>
  qexistsl_tac [`ce`, `dst`, `ZIP (vs,tys)`, `s`, `tops`] >>
  simp[SIMP_RULE bool_ss [combinTheory.o_DEF] EVERY_FST_ZIP]
QED

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
  >~ [`Extract32`] >- suspend "extract32"
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

Resume runtime_sym_type_builtin_body[extract32]:
  `?a b. args = [a;b]` by
    (namedCases_on `args` ["", "a rest"] >>
     gvs[runtime_sym_type_builtin_domain, supported_type_builtin_form_def] >>
     namedCases_on `rest` ["", "b others"] >> gvs[] >>
     Cases_on `others` >> gvs[]) >>
  gvs[] >>
  `!e t s op s'. (e = a \/ e = b) /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce t e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >> drule runtime_sym_generators_lower_value >>
     simp[runtime_sym_lower_value_clause_def] >> strip_tac >> first_x_assum irule >>
     goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     gvs[supported_exprs_exists_every] >>
     simp[supportedExprsTheory.supported_expr_def]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ output` >>
  Cases_on `output` >> simp[NoAsms, as_stack_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand src_mem` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _`
       (qspecl_then [`a`,`expr_type a`,`s`,`src_mem`,`st1`] mp_tac) >>
     simp[]) >>
  drule_all runtime_sym_bytestring_src >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand off_op` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _`
       (qspecl_then [`b`,`ty`,`st2`,`off_op`,`st3`] mp_tac) >>
     simp[]) >>
  drule_all runtime_sym_extract32_load >> strip_tac >>
  drule_all runtime_sym_extract32_clamp >> simp[runtime_sym_value_def]
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
      simp[as_ptr_val_def] >>
      strip_tac >> gvs[] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      simp[runtime_sym_value_def, mk_ptr_def]) >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `rt` >> simp[] >>
  FIRST [qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory cv`,
         qmatch_goalsub_abbrev_tac `as_stack_val vt cv`] >>
  Cases_on `cv` >> simp[as_stack_val_def, as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def, is_label_operand_def]
QED
Resume runtime_sym_type_builtin_body[encode]:
  drule runtime_sym_generators_abi >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_abi_clauses_def]) >>
  drule runtime_sym_generators_abi_encode_args >>
  disch_then (assume_tac o SRULE [runtime_sym_abi_encode_args_clause_def]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_type_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory encoded_pair` >>
  Cases_on `encoded_pair` >> simp[NoAsms, as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  rename1 `compile_abi_encode_args cfn ce args s = (vs,st)` >>
  `LENGTH vs = LENGTH args` by
    (qspec_then `s` mp_tac (Q.SPECL [`args`, `cfn`, `ce`]
      exprLoweringPropsTheory.compile_abi_encode_args_length) >> simp[]) >>
  qpat_x_assum `!cfn ce es s ops s'. _ ==> _`
    (drule_at_then (Pat `compile_abi_encode_args _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!mid n encode s op s'. _ ==> _`
    (drule_at_then (Pat `lower_abi_encode _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def] >> disch_then irule >>
  rpt gen_tac >> strip_tac >> irule runtime_sym_abi_encode_payload >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `vs` >> gvs[] >> qexists_tac `tops` >> first_assum ACCEPT_TAC
QED
Resume runtime_sym_type_builtin_body[decode]:
  `?e. args = [e]` by
    (Cases_on `args` >> gvs[runtime_sym_type_builtin_domain, supported_type_builtin_form_def] >>
     Cases_on `t` >>
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
  pairarg_tac >>
  qpat_assum `cfn _ _ _ _ = _` (fn th => simp[NoAsms, th]) >>
  pairarg_tac >>
  qpat_assum `unwrap_value _ _ _ = _` (fn th => simp[NoAsms, th]) >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory decoded_pair` >>
  Cases_on `decoded_pair` >> simp[NoAsms, as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  qpat_x_assum `Abbrev _` (assume_tac o SYM o SRULE [markerTheory.Abbrev_def]) >>
  `supported_expr tops e` by
    (rewrite_tac[supportedExprsTheory.supported_expr_def] >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  `~supported_expr_exists is_self_code e` by fs[supported_exprs_exists_every] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value data_vv` by
    (first_x_assum (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >>
     simp[] >> gvs[supported_exprs_exists_every, supportedExprsTheory.supported_expr_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Finalise runtime_sym_type_builtin_body

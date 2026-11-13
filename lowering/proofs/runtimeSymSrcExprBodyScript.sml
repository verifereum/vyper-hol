Theory runtimeSymSrcExprBody
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcEmissionProbe exprLowering compileEnv context emitHelper
  supportedExprs supportedExprTraverse exprCallBounds exprSimHypsDefs vyperAST list venomInst stackPlanTypes finite_map

Theorem runtime_sym_expr_body:
  runtime_sym_generator_contracts tops /\
  (!ce t child. expr_size child < expr_size e ==>
     runtime_sym_expr_contract tops cfn ce t child) /\
  (!ce rt t bi es. list_size expr_size es < expr_size e ==>
     runtime_sym_builtin_contract tops bfn ce rt t bi es) /\
  (!ce vt t tb rt es. list_size expr_size es < expr_size e ==>
     runtime_sym_type_builtin_contract tops tfn ce vt t tb rt es) ==>
  runtime_sym_expr_contract tops (compile_expr_body cfn bfn tfn) ce ty e
Proof
  strip_tac >> Cases_on `e`
  >~ [`Literal rt lit`] >- suspend "literal"
  >~ [`Name rt n`] >- suspend "name"
  >~ [`IfExp rt c a b`] >- suspend "ifexp"
  >~ [`Builtin rt bi es`] >- suspend "builtin"
  >~ [`TypeBuiltin rt tb target es`] >- suspend "typebuiltin"
  >~ [`Subscript rt a b`] >- suspend "subscript"
  >~ [`Attribute rt a fld`] >- suspend "attribute"
  >~ [`StructLit rt ns fields`] >- suspend "struct"
  >~ [`FlagMember rt ns fld`] >- suspend "flag"
  >~ [`TopLevelName rt ns`] >- suspend "topname"
  >~ [`Call rt target es default`] >- suspend "call"
  >~ [`Pop rt target`] >- suspend "pop"
QED

Resume runtime_sym_expr_body[literal]:
  drule runtime_sym_generators_expr_primitive >>
  pure_rewrite_tac[runtime_sym_expr_primitive_clauses_def] >>
  disch_then (assume_tac o cj 1) >>
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def,
       expr_type_def] >> metis_tac[]
QED
Resume runtime_sym_expr_body[name]:
  simp[runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  metis_tac[runtime_sym_compile_name]
QED
Resume runtime_sym_expr_body[ifexp]:
  drule runtime_sym_generators_lower_value >>
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> disch_tac >>
  drule runtime_sym_generators_context >>
  pure_rewrite_tac[runtime_sym_context_clauses_def] >>
  disch_then (assume_tac o cj 2) >>
  `!t. runtime_sym_expr_contract tops cfn ce t c /\
       runtime_sym_expr_contract tops cfn ce t a /\
       runtime_sym_expr_contract tops cfn ce t b` by
    (gen_tac >> rpt conj_tac >> first_x_assum irule >> simp[expr_size_def]) >>
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def,
       supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ce t child. _ ==> runtime_sym_expr_contract _ _ _ _ _` kall_tac >>
  qpat_x_assum `!ce rt' t bi es. _ ==> runtime_sym_builtin_contract _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!ce vt t tb rt' es. _ ==> runtime_sym_type_builtin_contract _ _ _ _ _ _ _ _` kall_tac >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `!cfn ce ty e s op s'. _`
    (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[supported_expr_def, supported_expr_exists_def] >> strip_tac >>
  drule runtime_sym_fresh_var >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >>
  gvs[supported_expr_exists_def] >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jnz >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `EVERY runtime_sym_inst (state_insts st7)` by
    metis_tac[runtime_sym_new_block, pairTheory.SND] >>
  suspend "ifexp_arms"
QED
Resume runtime_sym_expr_body[builtin]:
  `runtime_sym_builtin_contract tops bfn ce rt ty bi es` by
    (first_x_assum irule >> simp[expr_size_def]) >>
  qpat_x_assum `!ce t child. _ ==> runtime_sym_expr_contract _ _ _ _ _` kall_tac >>
  qpat_x_assum `!ce rt' t bi es'. _ ==> runtime_sym_builtin_contract _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!ce vt t tb rt' es'. _ ==> runtime_sym_type_builtin_contract _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `names_builtin bi es`
  >- (pop_assum mp_tac >>
      qpat_x_assum `runtime_sym_builtin_contract _ _ _ _ _ _ _` kall_tac >>
      drule runtime_sym_generators_name_fastpath >>
      pure_rewrite_tac[runtime_sym_name_fastpath_clauses_def] >> strip_tac >>
      qid_spec_tac `es` >> qid_spec_tac `bi` >>
      recInduct names_builtin_ind >> simp[NoAsms, names_builtin_def] >>
      rpt strip_tac >>
      simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
      metis_tac[]) >>
  simp[runtime_sym_expr_contract_def, compile_expr_body_builtin_dispatch] >>
  gvs[runtime_sym_builtin_contract_def, supported_expr_def,
      supported_pure_expr_def, supported_effect_expr_def] >> metis_tac[]
QED
Resume runtime_sym_expr_body[typebuiltin]:
  simp[runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  first_x_assum (qspecl_then [`ce`, `rt`, `ty`, `tb`, `target`, `es`] mp_tac) >>
  simp[expr_size_def, runtime_sym_type_builtin_contract_def,
       supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED
Resume runtime_sym_expr_body[subscript]:
  drule runtime_sym_generators_subscript >>
  pure_rewrite_tac[runtime_sym_subscript_clause_def] >> disch_tac >>
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  rpt gen_tac >> disch_tac >>
  `!t. runtime_sym_expr_contract tops cfn ce t a /\
       runtime_sym_expr_contract tops cfn ce t b` by
    (gen_tac >> conj_tac >> first_x_assum irule >> simp[expr_size_def]) >>
  metis_tac[]
QED
Resume runtime_sym_expr_body[attribute]:
  drule runtime_sym_generators_attribute >>
  pure_rewrite_tac[runtime_sym_attribute_clause_def] >> disch_tac >>
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  rpt gen_tac >> disch_tac >>
  `runtime_sym_expr_contract tops cfn ce ty a` by
    (first_x_assum irule >> simp[expr_size_def]) >> metis_tac[]
QED
Resume runtime_sym_expr_body[struct]:
  drule runtime_sym_generators_struct_lit >>
  pure_rewrite_tac[runtime_sym_struct_lit_clause_def] >> disch_tac >>
  drule runtime_sym_generators_context >>
  pure_rewrite_tac[runtime_sym_context_clauses_def] >>
  disch_then (assume_tac o cj 3) >>
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  rpt gen_tac >> strip_tac >>
  `!e t. MEM e (MAP SND fields) ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[MEM_MAP] >> Cases_on `y` >> gvs[] >>
     drule expr_struct_field_bound >>
     disch_then (qspecl_then [`ns`, `rt`] mp_tac) >>
     simp[NoAsms, expr_size_def]) >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!n s b s'. _ /\ compile_alloc_buffer n s = (b,s') ==> _`
    (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  simp[] >> strip_tac >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
      supported_expr_exists_def] >>
  qpat_x_assum `!cfn ce ty fields buf off s op s'. _`
    (drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)) >>
  simp[GSYM supported_pure_fields_every] >> strip_tac >>
  simp[runtime_sym_value_def, base_ptr_def]
QED
Resume runtime_sym_expr_body[flag]:
  simp[runtime_sym_expr_contract_def, supported_expr_def,
       supported_pure_expr_def, supported_effect_expr_def, supported_pure_expr_def]
QED
Resume runtime_sym_expr_body[topname]:
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  Cases_on `FLOOKUP ce.ce_module_vars ns` >>
  simp[NoAsms, runtime_sym_value_def, mk_ptr_def, is_label_operand_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  TRY (Cases_on `x` >> gvs[runtime_sym_value_def, mk_ptr_def, is_label_operand_def]) >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_inst_def, mk_inst_def, runtime_sym_value_def,
       is_label_operand_def]
QED
Resume runtime_sym_expr_body[call]:
  drule runtime_sym_generators_call >>
  pure_rewrite_tac[runtime_sym_call_clause_def] >> disch_tac >>
  simp[NoAsms, runtime_sym_expr_contract_def, compile_expr_body_def, expr_type_def] >>
  `!e t. MEM e es \/ default = SOME e ==>
     runtime_sym_expr_contract tops cfn ce t e` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule
     >- metis_tac[expr_call_arg_bound]
     >> gvs[] >> simp[expr_call_default_bound]) >>
  simp[NoAsms, supported_pure_expr_def, supported_expr_def,
       supported_effect_expr_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[supported_expr_def] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume runtime_sym_expr_body[pop]:
  simp[NoAsms, runtime_sym_expr_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `target` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
      supported_expr_exists_def] >>
  drule runtime_sym_generators_target_ptr >>
  pure_rewrite_tac[runtime_sym_target_ptr_clause_def] >> disch_tac >>
  drule runtime_sym_generators_expr_primitive >>
  pure_rewrite_tac[runtime_sym_expr_primitive_clauses_def] >>
  disch_then (assume_tac o cj 7) >>
  gvs[compile_expr_body_def, expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!cfn ce target s op loc pt s'. _`
    (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)) >>
  simp[supported_expr_exists_def] >> strip_tac >>
  qpat_x_assum `!base ws size ctor imm loc s op s'. _`
    (drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)) >>
  gvs[runtime_sym_env_def] >> strip_tac >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_expr_body[ifexp_arms]:
  qpat_x_assum `!t. runtime_sym_expr_contract _ _ _ _ _ /\ _`
    (qspec_then `ty` strip_assume_tac) >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `runtime_sym_expr_contract tops cfn ce ty a` mp_tac >>
  simp[NoAsms, runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `cfn _ _ _ _ = _`)) >>
  simp[supported_expr_def] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  qpat_assum `!ce rt at v s op s'. _`
    (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_labeled_inst] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `EVERY runtime_sym_inst (state_insts st11)` by
    metis_tac[runtime_sym_new_block, pairTheory.SND] >>
  suspend "ifexp_else"
QED
Resume runtime_sym_expr_body[ifexp_else]:
  pairarg_tac >> gvs[] >>
  qpat_x_assum `runtime_sym_expr_contract tops cfn ce ty b` mp_tac >>
  simp[NoAsms, runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `cfn _ _ _ _ = _`)) >>
  simp[supported_expr_def] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  qpat_assum `!ce rt at v s op s'. _`
    (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_labeled_inst] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `EVERY runtime_sym_inst (state_insts st15)` by
    metis_tac[runtime_sym_new_block, pairTheory.SND] >>
  Cases_on `is_word_type rt` >>
  gvs[runtime_sym_value_def, mk_ptr_def, is_label_operand_def]
QED
Finalise runtime_sym_expr_body

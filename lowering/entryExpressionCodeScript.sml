Theory entryExpressionCode
Ancestors
  entryDispatcherCode entryCallCode entryAggregateCode entryValueCode
  entryArithmeticCode entryBuiltinCode entryCodePredicate entryContextCodePredicate
  exprLowering exprCallBounds supportedExprs exprSimHypsDefs

Theorem entry_code_invalid_expr[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (invalid_expr_call ty)
Proof
  rw[entry_preserves_code_def, invalid_expr_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `INVALID`] entry_code_emit_inst))
QED

Theorem entry_code_expr_callback[local]:
  (expr_size e < bound ==>
   entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (expr_child_callback bound cfn ce ty e)
Proof
  rw[entry_preserves_code_def, expr_child_callback_def] >>
  metis_tac[entry_preserves_code_def, entry_code_invalid_expr]
QED

Theorem entry_code_ifexp_body[local]:
  (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et c)) /\
  (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et a)) /\
  (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et b)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_expr_body cfn bfn tfn ce ty (IfExp ann c a b))
Proof
  strip_tac >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (lower_value cfn ce (BaseT BoolT) c)` by
    (irule entry_code_lower_value >> simp[]) >>
  rw[entry_preserves_code_def, compile_expr_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!ce et. entry_preserves_code _ (cfn ce et a)`
    (qspecl_then [`ce`, `ty`] (fn th =>
      imp_res_tac (SRULE [entry_preserves_code_def] th))) >>
  qpat_x_assum `!ce et. entry_preserves_code _ (cfn ce et b)`
    (qspecl_then [`ce`, `ty`] (fn th =>
      imp_res_tac (SRULE [entry_preserves_code_def] th))) >>
  qpat_x_assum `entry_preserves_code _ (lower_value _ _ _ _)`
    (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [Q.INST [`P` |-> `\i. i.inst_opcode <> DALLOCA`] entry_code_fresh_var,
     Q.INST [`P` |-> `\i. i.inst_opcode <> DALLOCA`] entry_code_fresh_label,
     Q.INST [`P` |-> `\i. i.inst_opcode <> DALLOCA`] entry_code_new_block,
     entry_code_ifexp_arm] >>
  map_every (fn opc => imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> opc] entry_code_emit_inst))) [`JNZ`, `ASSIGN`, `JMP`] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem entry_code_struct_body[local]:
  (!name e ce et. MEM (name,e) fields ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_expr_body cfn bfn tfn ce ty (StructLit ann ns fields))
Proof
  strip_tac >> rw[entry_preserves_code_def, compile_expr_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule entry_code_struct_lit >>
  disch_then (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_alloc_buffer) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Theorem entry_code_builtin_body[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (bfn ce ann ty bi args) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_expr_body cfn bfn tfn ce ty (Builtin ann bi args))
Proof
  strip_tac >> Cases_on `names_builtin bi args`
  >- (namedCases_on `args` ["", "a rest"] >> gvs[names_builtin_def] >>
      Cases_on `a` >> gvs[names_builtin_def] >>
      namedCases_on `rest` ["", "b rest2"] >> gvs[names_builtin_def] >>
      Cases_on `b` >> gvs[names_builtin_def] >>
      namedCases_on `rest2` ["", "c rest3"]
      >- (Cases_on `bi` >> gvs[names_builtin_def] >>
          rw[entry_preserves_code_def, compile_expr_body_def] >>
          imp_res_tac (SRULE [entry_preserves_code_def] entry_code_powmod256_names)) >>
      Cases_on `c` >> gvs[names_builtin_def] >>
      Cases_on `rest3` >> Cases_on `bi` >> gvs[names_builtin_def] >>
      rw[entry_preserves_code_def, compile_expr_body_def] >>
      map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
        [entry_code_addmod_names, entry_code_mulmod_names, entry_code_powmod256_names]) >>
  rw[entry_preserves_code_def] >>
  gvs[compile_expr_body_builtin_dispatch] >>
  metis_tac[entry_preserves_code_def]
QED

Theorem entry_code_expr_equation[local]:
  compile_expr ce ty e =
    compile_expr_body
      (expr_child_callback (expr_size e) compile_expr)
      (builtin_child_callback (expr_size e) compile_builtin_dispatch)
      (type_child_callback (expr_size e) compile_type_builtin_dispatch) ce ty e
Proof
  simp[Once FUN_EQ_THM, Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem entry_code_dynarray_pop[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_dynarray_pop base_op ws sz ctor imm loc)
Proof
  simp[compile_dynarray_pop_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >>
    simp[entry_code_ptr_load, entry_code_ptr_store, entry_code_emit_op,
         entry_code_emit_void] >> rpt gen_tac)
QED

Theorem entry_code_supported_union[local]:
  !e cenv ty.
    (supported_pure_expr tops e \/ supported_place_expr tops e \/
     supported_effect_expr tops e \/ supported_effect_place_expr tops e) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr cenv ty e)
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >>
  disch_tac >>
  `!ce et child. expr_size child < expr_size e /\
     (supported_pure_expr tops child \/ supported_place_expr tops child \/
      supported_effect_expr tops child \/ supported_effect_place_expr tops child) ==>
     entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
       (expr_child_callback (expr_size e) compile_expr ce et child)` by
    (rpt strip_tac >> irule entry_code_expr_callback >> metis_tac[]) >>
  pure_rewrite_tac[Once entry_code_expr_equation] >>
  Cases_on `e`
  >~ [`Name _ _`] >- suspend "name"
  >~ [`TopLevelName _ _`] >- suspend "top"
  >~ [`FlagMember _ _ _`] >- suspend "flag"
  >~ [`Literal _ _`] >- suspend "literal"
  >~ [`IfExp _ _ _ _`] >- suspend "ifexp"
  >~ [`StructLit _ _ _`] >- suspend "struct"
  >~ [`Subscript _ _ _`] >- suspend "subscript"
  >~ [`Attribute _ _ _`] >- suspend "attribute"
  >~ [`Builtin _ _ _`] >- suspend "builtin"
  >~ [`TypeBuiltin _ _ _ _`] >- suspend "type"
  >~ [`Pop _ _`] >- suspend "pop"
  >> suspend "call"
QED

Resume entry_code_supported_union[name]:
  rw[entry_preserves_code_def, compile_expr_body_def] >>
  metis_tac[entry_preserves_code_def, entry_code_name_vv]
QED

Resume entry_code_supported_union[literal]:
  rw[entry_preserves_code_def, compile_expr_body_def] >>
  metis_tac[entry_preserves_code_def, entry_code_literal_vv]
QED

Resume entry_code_supported_union[flag]:
  gvs[supported_pure_expr_def, supported_effect_expr_def]
QED

Resume entry_code_supported_union[top]:
  rw[entry_preserves_code_def, compile_expr_body_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `INVALID`] entry_code_emit_inst))
QED

Resume entry_code_supported_union[ifexp]:
  irule entry_code_ifexp_body >>
  gvs[supported_pure_expr_def, supported_effect_expr_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[vyperASTTheory.expr_size_def] >> metis_tac[]
QED

Resume entry_code_supported_union[subscript]:
  simp[entry_preserves_code_def, compile_expr_body_def] >>
  pure_rewrite_tac[GSYM entry_preserves_code_def] >> irule entry_code_subscript >>
  gvs[supported_pure_expr_def, supported_effect_expr_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[vyperASTTheory.expr_size_def] >> metis_tac[]
QED

Resume entry_code_supported_union[attribute]:
  simp[entry_preserves_code_def, compile_expr_body_def] >>
  pure_rewrite_tac[GSYM entry_preserves_code_def] >> irule entry_code_attribute >>
  gvs[supported_pure_expr_def, supported_effect_expr_def] >>
  first_x_assum irule >> simp[vyperASTTheory.expr_size_def] >> metis_tac[]
QED

Resume entry_code_supported_union[struct]:
  irule entry_code_struct_body >>
  gvs[supported_pure_expr_def, supported_effect_expr_def] >>
  rpt strip_tac >> first_x_assum irule >>
  conj_tac
  >- (drule expr_struct_field_bound >> simp[vyperASTTheory.expr_size_def]) >>
  fs[supported_pure_fields_every, listTheory.EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Resume entry_code_supported_union[builtin]:
  irule entry_code_builtin_body >>
  simp[entry_preserves_code_def, builtin_child_callback_def,
       expr_builtin_dispatch_bound, Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  pure_rewrite_tac[GSYM entry_preserves_code_def] >>
  irule (Q.INST [`tops` |-> `tops`] entry_code_builtin_dispatch_body) >>
  gvs[supported_pure_expr_def, supported_effect_expr_def] >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  irule entry_code_expr_callback >> strip_tac >>
  first_x_assum irule >>
  conj_tac
  >- (drule expr_list_member_bound >> simp[vyperASTTheory.expr_size_def]) >>
  fs[supported_pure_exprs_every, listTheory.EVERY_MEM] >> metis_tac[]
QED

Resume entry_code_supported_union[type]:
  simp[entry_preserves_code_def, compile_expr_body_def,
       type_child_callback_def, expr_builtin_dispatch_bound,
       Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  pure_rewrite_tac[GSYM entry_preserves_code_def] >>
  irule entry_code_type_builtin_dispatch_body >>
  gvs[supported_pure_expr_def, supported_effect_expr_def, vyperASTTheory.expr_type_def] >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  irule entry_code_expr_callback >> strip_tac >>
  first_x_assum irule >> conj_tac
  >- (drule expr_list_member_bound >> simp[vyperASTTheory.expr_size_def]) >>
  fs[supported_pure_exprs_every, listTheory.EVERY_MEM] >> metis_tac[]
QED

Resume entry_code_supported_union[call]:
  simp[entry_preserves_code_def, compile_expr_body_def] >>
  pure_rewrite_tac[GSYM entry_preserves_code_def] >>
  irule entry_code_supported_call >>
  reverse conj_tac
  >- (gvs[supported_pure_expr_def, supported_effect_expr_def] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[supported_pure_expr_def, supported_effect_expr_def, vyperASTTheory.expr_size_def] >>
  first_x_assum irule >> conj_tac
  >- (drule expr_call_arg_bound >> simp[vyperASTTheory.expr_size_def]) >>
  qpat_x_assum `supported_effect_expr tops (Call _ _ _ _)` mp_tac >>
  Cases_on `c` >> Cases_on `o'` >>
  simp[supported_effect_expr_def] >>
  rpt strip_tac >> gvs[supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  disj1_tac
  >~ [`supported_effect_expr tops (Call _ (ExtCall _ _ p _) _ _)`]
  >- (PairCases_on `p` >> gvs[supported_effect_expr_def,
        supported_pure_exprs_every, listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `t` >> Cases_on `b` >>
  namedCases_on `l` ["", "a rest"] >> gvs[supported_effect_expr_def] >>
  namedCases_on `rest` ["", "v rest2"] >> gvs[supported_effect_expr_def] >>
  namedCases_on `rest2` ["", "g rest3"] >> gvs[supported_effect_expr_def] >>
  Cases_on `rest3` >> gvs[supported_effect_expr_def] >> metis_tac[]
QED

Resume entry_code_supported_union[pop]:
  gvs[supported_pure_expr_def, supported_effect_expr_def] >>
  rename1 `Pop ann target` >> Cases_on `target` >>
  gvs[supported_effect_expr_def] >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_get_target_ptr
       (expr_child_callback (expr_size (Pop ann (TopLevelNameTarget p))) compile_expr)
       cenv (TopLevelNameTarget p))` by
    (irule entry_code_get_target_ptr >> simp[targetPlaceSimCasesTheory.target_indices_def]) >>
  rw[entry_preserves_code_def, compile_expr_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `entry_preserves_code _ (compile_get_target_ptr _ _ _)`
    (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_dynarray_pop) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Finalise entry_code_supported_union

Theorem entry_code_supported_pure_expr:
  supported_pure_expr tops e ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr cenv ty e)
Proof
  metis_tac[entry_code_supported_union]
QED

Theorem entry_code_supported_place_expr:
  supported_place_expr tops e ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr cenv ty e)
Proof
  metis_tac[entry_code_supported_union]
QED

Theorem entry_code_supported_effect_expr:
  supported_effect_expr tops e ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr cenv ty e)
Proof
  metis_tac[entry_code_supported_union]
QED

Theorem entry_code_supported_effect_place_expr:
  supported_effect_place_expr tops e ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr cenv ty e)
Proof
  metis_tac[entry_code_supported_union]
QED

Theorem entry_code_supported_expr:
  supported_expr tops e ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr cenv ty e)
Proof
  simp[supported_expr_def] >> metis_tac[entry_code_supported_union]
QED

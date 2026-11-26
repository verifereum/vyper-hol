(* Source and paired compiler cuts for linked Convert from bytes to a scalar. *)
Theory bodyConvertDynamicEntryMods
Ancestors
  bodyFullPredsMods bodyTypeBuiltinAbiMods exprBodyPreProps bodyFullShared
  exprSimConvertFromBytes exprSimConvert exprLowering exprLoweringProps
  exprBopLowering gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowState
  gasShadow externalEntryShape fragExec
  compileEnv vyperTypeSystem vyperContext vyperInterpreter vyperState vyperAST

Theorem dynamic_convert_entry_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst ==>
  ann = dst /\ is_word_type dst /\ (!n. dst <> FlagT n) /\
  valid_conversion (expr_type e) dst /\ well_formed_type env.type_defs dst /\
  expr_body_pre_mods mods ce cx env e es
Proof
  strip_tac >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_type_builtin_args_def,
       type_builtin_result_ok_def] >> strip_tac >> gvs[] >>
  drule_all dynamic_scalar_type >> strip_tac >> simp[] >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  irule type_builtin_body_arg_pre_mods >>
  simp[] >> qexistsl_tac [`ann`,`[e]`,`es`,`Convert`,`ann`] >> simp[]
QED

Theorem dynamic_convert_compile_cut:
  is_bytestring_type (expr_type e) /\ is_word_type dst /\
  ~is_bytestring_type dst /\ (!n. dst <> FlagT n) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) ==>
  compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    if lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
       lowered_value_type ce e = BaseT (StringT 0) then
      (StackValue dst (Lit 0w),sm)
    else as_stack_val dst
          (compile_type_convert op (mk_convert_op (expr_type e) dst) sm)
Proof
  strip_tac >>
  simp[Once (cj 1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (cj 3 compile_expr_raw_def), compile_type_builtin_dispatch_body_def,
       exprCallBoundsTheory.expr_child_callback_def] >>
  simp[lower_value_child_call, SF ETA_ss, expr_type_def] >>
  Cases_on `dst` >> gvs[is_word_type_def]
QED

Theorem dynamic_convert_source_action:
  eval_expr cx (TypeBuiltin dst Convert dst [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (sum_CASE (convert_result cx (expr_type e) dst v)
         (\w. INL (Value w)) INR, ee))
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac `es` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,ee)` >>
  Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
  Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val dst` >>
  simp[return_def, raise_def]
QED

Theorem dynamic_convert_paired_cut_mods:
  is_bytestring_type (expr_type e) /\ is_word_type dst /\
  ~is_bytestring_type dst /\ (!n. dst <> FlagT n) /\
  compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (TypeBuiltin dst Convert dst [e])) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op sm shadow_sm.
    lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\
    cs_extends sa sm /\ cs_extends shadow_sa shadow_sm /\
    fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
    (if lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type ce e = BaseT (StringT 0) then
       vv = StackValue dst (Lit 0w) /\ sb = sm /\ shadow_sb = shadow_sm
     else ?out. vv = StackValue dst out /\
       compile_type_convert op (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
       compile_type_convert op (mk_convert_op (expr_type e) dst) shadow_sm = (out,shadow_sb) /\
       cs_extends sm sb /\ cs_extends shadow_sm shadow_sb /\
       fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func)
Proof
  strip_tac >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `_ = (op,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >> rename1 `_ = (sop,shadow_sm)` >>
  `sop = op /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >> simp[] >>
     qexistsl_tac [`lower_value compile_expr ce (expr_type e) e`,
       `lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e)`,
       `sa`,`shadow_sa`] >> simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cj 2 compile_expr_grows] >>
  `compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    if lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
       lowered_value_type ce e = BaseT (StringT 0) then
      (StackValue dst (Lit 0w),sm)
    else as_stack_val dst
          (compile_type_convert op (mk_convert_op (expr_type e) dst) sm)` by
    (irule dynamic_convert_compile_cut >> simp[]) >>
  `compile_expr (gas_shadow_env T ce) ty
    (TypeBuiltin dst Convert dst [gas_shadow_expr e]) shadow_sa =
    if lowered_value_type (gas_shadow_env T ce) (gas_shadow_expr e) = BaseT (BytesT (Dynamic 0)) \/
       lowered_value_type (gas_shadow_env T ce) (gas_shadow_expr e) = BaseT (StringT 0) then
      (StackValue dst (Lit 0w),shadow_sm)
    else as_stack_val dst (compile_type_convert op
          (mk_convert_op (expr_type (gas_shadow_expr e)) dst) shadow_sm)` by
    (irule dynamic_convert_compile_cut >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >>
  Cases_on `lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type ce e = BaseT (StringT 0)`
  >- gvs[] >>
  Cases_on `compile_type_convert op (mk_convert_op (expr_type e) dst) sm` >>
  rename1 `_ = (out,sf)` >>
  Cases_on `compile_type_convert op (mk_convert_op (expr_type e) dst) shadow_sm` >>
  rename1 `_ = (shadow_out,shadow_sf)` >>
  gvs[as_stack_val_pair] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[cj 1 compile_type_convert_labels, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  simp[]
QED

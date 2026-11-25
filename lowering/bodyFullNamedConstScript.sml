(* Named constants forward the execution of the fresh value they wrap. *)
Theory bodyFullNamedConst
Ancestors
  bodyFullPreds bodyFullOfVV namedConstLoweredType bodyFullExprGeneric
  exprSimSource exprSimConvert exprBodyPreProps exprSimProps exprLoweringProps
  gasShadowCompile gasOutcomeFullCompose exprSimMemDefs exprSafeOperandBuiltins
  exprLowering loweringPosts vyperTypeSystem vyperContext vyperState vyperInterpreter
  exprReasonOperand exprSimAggregateLayout exprOperandVar exprSimHyps
  namesBuiltinExclusions
  abiEmptyDispatch abiEmptyAllocate exprSafeOperand compileEnv context
  bodySimFull bodyPtrDefs gasOutcomeFull gasShadowState gasShadow
  exprSimHypsDefs vyperAST exprCallBounds
Libs
  pairLib

Theorem named_const_operand_eval_value[local]:
  named_const_operand e /\ eval_expr cx e st = (INL r,st') ==>
  ?v. r = Value v
Proof
  Cases_on `e` >> simp[oneline named_const_operand_def] >>
  metis_tac[eval_expr_literal_value, eval_expr_builtin_value,
            eval_expr_type_builtin_value]
QED

Theorem named_const_eval[local]:
  named_const_operand e ==>
  eval_expr cx (Builtin ann NamedConst [e]) = eval_expr cx e
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  simp[Once evaluate_def, builtin_args_length_ok_def, code_slice_source_def,
       is_self_codesize_def, type_check_def, assert_def, ignore_bind_def,
       return_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `_ = (res,st')` >> Cases_on `res` >>
  gvs[] >> drule_all named_const_operand_eval_value >> strip_tac >>
  simp[read_result_def, return_def, Once evaluate_def, get_accounts_def,
       evaluate_builtin_def, lift_sum_def, precompile_call_success_def,
       bind_def, ignore_bind_def]
QED

(* These operand forms produce their own storage, or a plain word. *)
Theorem named_const_literal_shape[local]:
  well_typed_literal ann l /\ well_formed_type tenv ann /\
  compile_literal_vv ann l sa = (vv,sb) ==>
  if is_word_type ann then ?op. vv = StackValue ann op /\ !n. op <> Label n
  else ?p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory /\
           !n. p.ptr_operand <> Label n
Proof
  strip_tac >> drule reason_compile_literal >> strip_tac >>
  Cases_on `l` >> Cases_on `ann` >> gvs[well_typed_literal_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[well_typed_literal_def] >>
  simp[is_word_type_def] >>
  gvs[compile_literal_vv_def, comp_return_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[reason_result_shape_def, base_ptr_def]
  >~ [`BoolL b`] >-
    (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[well_typed_literal_def, is_word_type_def, comp_return_def, comp_bind_def]
  >- gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  pairarg_tac >> gvs[reason_result_shape_def]
QED

Theorem named_const_operand_shape[local]:
  named_const_operand e /\ well_typed_expr env e /\
  compile_expr cenv ty e sa = (vv,sb) ==>
  if is_word_type (expr_type e) then
    ?op. vv = StackValue (expr_type e) op /\ !n. op <> Label n
  else
    ?p. vv = LocatedValue (expr_type e) p /\ p.ptr_location = LocMemory /\
        !n. p.ptr_operand <> Label n
Proof
  strip_tac >> Cases_on `e` >> gvs[oneline named_const_operand_def]
  >~ [`Literal ann l`] >-
    (gvs[well_typed_expr_def, expr_type_def, Once compile_expr_component_eq] >>
     metis_tac[named_const_literal_shape])
  >~ [`Builtin ann bi args`] >-
    (rename1 `compile_expr _ _ (Builtin ann bi args) _ = _` >>
     Cases_on `bi` >> gvs[] >>
     rename1 `MakeArray et bd` >> Cases_on `et` >>
     gvs[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def, is_word_type_def]
     >- (drule compile_tuple_literal_inv >> strip_tac >> gvs[mk_ptr_def] >>
         drule compiler_make_tuple_result >> strip_tac >> gvs[] >>
         drule alloc_buffer_safe_operand >> simp[safe_operand_def]) >>
     drule compile_array_literal_inv >> strip_tac >> gvs[mk_ptr_def] >>
     drule compiler_make_array_result >> strip_tac >> gvs[] >>
     drule alloc_buffer_safe_operand >> simp[safe_operand_def]) >>
  rename1 `compile_expr _ _ (TypeBuiltin ann tb rt args) _ = _` >>
  Cases_on `tb` >> Cases_on `args` >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def] >>
  qpat_x_assum `compile_expr _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[expr_type_def, Once compile_expr_component_eq] >>
  simp[Once compile_type_builtin_dispatch_component_eq] >>
  IF_CASES_TAC >> simp[] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[base_ptr_def] >>
  drule abi_empty_complex_parts >> strip_tac >>
  drule alloc_buffer_safe_operand >> simp[safe_operand_def]
QED

Theorem compile_named_const[local]:
  lower_value compile_expr cenv ty e sa = (op,sb) /\ (!n. op <> Label n) ==>
  compile_expr cenv ty (Builtin ann NamedConst [e]) sa =
    ((if is_word_type ann then StackValue ann op
      else LocatedValue ann (mk_ptr op LocMemory)),sb)
Proof
  strip_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_exclusions] >>
  simp[Once compile_builtin_dispatch_component_eq] >>
  fs[lower_value_def, comp_bind_def] >>
  simp[listTheory.list_size_def, lower_value_def, comp_bind_def,
       arithmeticTheory.ADD_ASSOC] >>
  Cases_on `op` >> gvs[as_ptr_val_def, as_stack_val_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem named_const_parent_compile[local]:
  (!n. vv_operand vv <> Label n) /\
  (if is_word_type ann then ?op. vv = StackValue ann op
   else ?p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory) /\
  compile_expr cenv ty e sa = (vv,sb) ==>
  compile_expr cenv ty (Builtin ann NamedConst [e]) sa =
  ((if is_word_type ann then vv
    else LocatedValue ann (mk_ptr (vv_operand vv) LocMemory)),sb)
Proof
  strip_tac >>
  `lower_value compile_expr cenv ty e sa = (vv_operand vv,sb)` by
    (Cases_on `is_word_type ann` >>
     gvs[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def, vv_operand_def]) >>
  drule_all compile_named_const >>
  Cases_on `is_word_type ann` >> gvs[vv_operand_def]
QED

Theorem named_const_post_type[local]:
  named_const_operand e ==> post_value_type cenv e = expr_type e
Proof
  Cases_on `e` >> simp[oneline named_const_operand_def, post_value_type_def]
QED

Theorem named_const_vv_full[local]:
  well_typed_expr env (Builtin ann NamedConst [e]) /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann NamedConst [e]) es
Proof
  strip_tac >>
  drule_then assume_tac lowered_value_type_named_const >>
  `expr_type e = ann /\ named_const_operand e /\ well_typed_expr env e` by
    gvs[well_typed_expr_def, well_typed_builtin_app_def, builtin_operands_ok_def] >>
  `post_value_type cenv e = ann` by simp[named_const_post_type] >>
  drule_then assume_tac named_const_eval >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (raw,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (shraw,shadow_sm)` >>
  `gas_shadow_compiles (compile_expr cenv ty e)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  `shraw = raw` by
    (qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  drule_all named_const_operand_shape >> simp[] >> strip_tac >>
  `(!n. vv_operand raw <> Label n) /\
   (if is_word_type ann then ?op. raw = StackValue ann op
    else ?p. raw = LocatedValue ann p /\ p.ptr_location = LocMemory)` by
    (Cases_on `is_word_type ann` >> gvs[vv_operand_def]) >>
  `compile_expr cenv ty (Builtin ann NamedConst [e]) sa =
    ((if is_word_type ann then raw
      else LocatedValue ann (mk_ptr (vv_operand raw) LocMemory)),sm)` by
    (irule named_const_parent_compile >> simp[]) >>
  `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin ann NamedConst [e])) shadow_sa =
    ((if is_word_type ann then raw
      else LocatedValue ann (mk_ptr (vv_operand raw) LocMemory)),shadow_sm)` by
    (simp[NoAsms, Once gas_shadow_expr_def, gas_shadow_builtin_def] >>
     irule named_const_parent_compile >> fs[]) >>
  gvs[] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`raw`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[expr_type_def] >>
  rpt gen_tac >> disch_then (qx_choose_then `tv` strip_assume_tac) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `is_word_type (expr_type e)` >> fs[] >>
  Cases_on `raw` >> gvs[vv_location_def, vv_operand_def, mk_ptr_def] >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, vv_place_ptr_def, vv_storage_live_def,
      vv_own_def, vv_store_bound_def, ptr_vv_ok_def, ptr_buf_ok_def, expr_type_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _`
    (qspecl_then [`aid`,`off`,`sz`] irule) >>
  rpt conj_tac >>> NTH_GOAL (metis_tac[]) 2 >>> NTH_GOAL (metis_tac[]) 3 >> first_assum ACCEPT_TAC
QED

Theorem named_const_expr_full_ok:
  !cx ann e. body_expr_full_ok cx e ==> body_expr_full_ok cx (Builtin ann NamedConst [e])
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_full_ok_def] >>
  rpt gen_tac >> strip_tac >> reverse conj_asm2_tac
  >- (drule_then strip_assume_tac expr_body_pre_static_facts >>
      `expr_body_pre cenv cx env e es` by
        (irule expr_body_pre_builtin_arg >> simp[] >>
         goal_assum (drule_at Any) >> simp[]) >>
      irule named_const_vv_full >> conj_tac
      >- (qexists_tac `env` >> simp[]) >>
      qpat_x_assum `body_expr_full_ok _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
      metis_tac[]) >>
  irule expr_sim_full_of_vv >> simp[post_value_type_def, expr_type_def] >> conj_tac
  >- (rpt strip_tac >>
      drule_then (mp_tac o REWRITE_RULE [expr_type_def]) expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS, expr_type_def] >>
  disch_then (qx_choose_then `tv` assume_tac) >>
  qexists_tac `tv` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin ann NamedConst [e]) (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[expr_type_def] >> metis_tac[]
QED

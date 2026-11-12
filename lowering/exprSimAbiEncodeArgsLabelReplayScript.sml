Theory exprSimAbiEncodeArgsLabelReplay
Ancestors
  abiArgsCompilerImage exprLowering exprCallBounds context compileEnv emitHelper
  exprSimMemorySource vyperInterpreter vyperContext
  vyperState vyperValue vyperAST vyperStatePreservation

Theorem abi_args_name_replay:
  bind (eval_expr cx (Name ann id)) (read_result cx) es = (INL v,ee) ==>
  !gs. bind (eval_expr cx (Name ann id)) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee with gas_obs := gs)
Proof
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def] >>
  Cases_on `IS_SOME (lookup_scopes id es.scopes)` >>
  simp[raise_def, bind_def, return_def] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule read_result_gas_obs >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def]
QED

Theorem abi_args_singleton_source[local]:
  eval_exprs cx [e] = bind (bind (eval_expr cx e) (read_result cx))
    (\v. return [v])
Proof
  simp[FUN_EQ_THM, Once evaluate_def, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def] >>
  rename1 `read_result cx a r` >> Cases_on `read_result cx a r` >>
  Cases_on `q` >> simp[Once evaluate_def, bind_def, return_def]
QED

Theorem abi_args_convert_replay:
  (!v ee. bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee with gas_obs := gs)) /\
  bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx) es =
    (INL v,ee) ==>
  !gs. bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee with gas_obs := gs)
Proof
  strip_tac >>
  qpat_x_assum `bind (eval_expr cx (TypeBuiltin _ _ _ _)) _ _ = _` mp_tac >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, abi_args_singleton_source] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) es` >>
  Cases_on `q` >>
  fs[vyperStateTheory.assert_def, bind_def, return_def] >>
  rename1 `evaluate_type_builtin cx Convert ty [expr_type e] [a]` >>
  Cases_on `evaluate_type_builtin cx Convert ty [expr_type e] [a]` >>
  simp[lift_sum_def, bind_def, return_def, raise_def, read_result_def] >>
  strip_tac >> gvs[] >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, abi_args_singleton_source,
       bind_def, return_def, lift_sum_def, read_result_def]
QED

Theorem abi_args_builtin_replay:
  bi <> Len /\ bi <> Env MsgGas /\ ~precompile_builtin bi /\
  builtin_args_length_ok bi 1 /\
  (!v ee. bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee with gas_obs := gs)) /\
  bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) es = (INL v,ee) ==>
  !gs. bind (eval_expr cx (Builtin ann bi [e])) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee with gas_obs := gs)
Proof
  strip_tac >>
  `bi <> Bop In /\ bi <> Bop NotIn` by
    (rpt strip_tac >> gvs[builtin_args_length_ok_def]) >>
  qpat_x_assum `bind (eval_expr cx (Builtin _ _ _)) _ _ = _` mp_tac >>
  simp[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
       abi_args_singleton_source] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) es` >>
  Cases_on `q` >> fs[assert_def, bind_def, return_def] >>
  simp[get_accounts_def, bind_def, return_def] >>
  rename1 `evaluate_builtin cx r.accounts ann bi [expr_type e] [a]` >>
  Cases_on `evaluate_builtin cx r.accounts ann bi [expr_type e] [a]` >>
  simp[get_accounts_def, lift_sum_def, bind_def, return_def, raise_def,
       read_result_def, ignore_bind_def] >>
  strip_tac >> gvs[] >>
  simp[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
       abi_args_singleton_source, bind_def, return_def, lift_sum_def,
       get_accounts_def, read_result_def]
QED

Theorem abi_args_builtin_success_arity:
  bind (eval_expr cx (Builtin ann bi args)) (read_result cx) es = (INL v,ee) ==>
  builtin_args_length_ok bi (LENGTH args)
Proof
  Cases_on `builtin_args_length_ok bi (LENGTH args)` >> simp[] >>
  simp[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
       bind_def, raise_def]
QED

Theorem abi_args_convert_success_arity:
  bind (eval_expr cx (TypeBuiltin ann Convert ty args)) (read_result cx) es =
    (INL v,ee) ==> LENGTH args = 1
Proof
  Cases_on `LENGTH args = 1` >> simp[] >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem abi_args_child_label_replay[local]:
  (!e ce ty sa vv sb l cx es v ee.
    expr_size e < bound /\ compile_expr ce ty e sa = (vv,sb) /\
    vv_operand vv = Label l /\
    bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee with gas_obs := gs)) /\
  lower_value (expr_child_callback bound compile_expr) ce ty e sa = (Label l,sb) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,ee with gas_obs := gs)
Proof
  simp[lower_value_def, comp_bind_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule abi_image_unwrap_label >> strip_tac >>
  Cases_on `expr_size e < bound`
  >- (gvs[expr_child_callback_def] >> metis_tac[]) >>
  gvs[expr_child_callback_def, invalid_expr_call_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[vv_operand_def])
QED

Theorem abi_args_label_replay_mutual:
  (!ce ty e sa vv sb l cx es v ee.
    compile_expr ce ty e sa = (vv,sb) /\ vv_operand vv = Label l /\
    bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee with gas_obs := gs)) /\
  (!ce ann ty bi args sa vv sb l cx es v ee.
    compile_builtin_dispatch ce ann ty bi args sa = (vv,sb) /\
    vv_operand vv = Label l /\
    bind (eval_expr cx (Builtin ann bi args)) (read_result cx) es = (INL v,ee) ==>
    !gs. bind (eval_expr cx (Builtin ann bi args)) (read_result cx)
      (es with gas_obs := gs) = (INL v,ee with gas_obs := gs)) /\
  (!ce ann ty tb rt args sa vv sb l cx es v ee.
    compile_type_builtin_dispatch ce ann ty tb rt args sa = (vv,sb) /\
    vv_operand vv = Label l /\
    bind (eval_expr cx (TypeBuiltin ann tb rt args)) (read_result cx) es =
      (INL v,ee) ==>
    !gs. bind (eval_expr cx (TypeBuiltin ann tb rt args)) (read_result cx)
      (es with gas_obs := gs) = (INL v,ee with gas_obs := gs))
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume abi_args_label_replay_mutual[expr]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  Cases_on `e`
  >~ [`eval_expr cx (Name _ _)`] >- metis_tac[abi_args_name_replay]
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _ = _`] >-
    (drule_all abi_image_expr_builtin_label >>
     simp[builtin_child_callback_def] >> strip_tac >>
     first_x_assum irule >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _ = _`] >-
    (gvs[compile_expr_body_def, expr_type_def, type_child_callback_def] >>
     first_x_assum irule >> simp[] >>
     goal_assum (drule_at (Pat `compile_type_builtin_dispatch`)) >> simp[])
  >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _ = _`] >-
    metis_tac[abi_image_toplevel_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (Pop _ _) _ = _`] >-
    metis_tac[abi_image_pop_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _ = _`] >-
    metis_tac[abi_image_struct_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _ = _`] >-
    metis_tac[abi_image_ifexp_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (FlagMember _ _ _) _ = _`] >-
    metis_tac[abi_image_flag_not_label] >>
  gvs[compile_expr_body_def, expr_type_def, LET_THM] >>
  metis_tac[abi_image_literal_not_label, abi_image_subscript_not_label,
            abi_image_attribute_not_label, abi_image_call_not_label]
QED

Resume abi_args_label_replay_mutual[builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  drule_all abi_image_builtin_label >> strip_tac >> gvs[] >>
  drule abi_args_builtin_success_arity >>
  simp[builtin_args_length_ok_def] >> strip_tac >>
  `?e. args = [e]` by (Cases_on `args` >> gvs[] >>
    Cases_on `t` >> gvs[]) >> gvs[] >>
  irule abi_args_builtin_replay >>
  simp[builtin_args_length_ok_def] >>
  rpt strip_tac >> irule abi_args_child_label_replay >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Resume abi_args_label_replay_mutual[type_builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  drule_all abi_image_type_builtin_label >> strip_tac >> gvs[] >>
  drule abi_args_convert_success_arity >> strip_tac >>
  `?e. args = [e]` by (Cases_on `args` >> gvs[] >>
    Cases_on `t` >> gvs[]) >> gvs[] >>
  irule abi_args_convert_replay >> conj_tac
  >- (rpt strip_tac >> irule abi_args_child_label_replay >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  goal_assum (drule_at Any)
QED

Finalise abi_args_label_replay_mutual

Theorem abi_args_lower_label_replay:
  lower_value compile_expr ce ty e sa = (Label l,sb) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,ee with gas_obs := gs)
Proof
  simp[lower_value_def, comp_bind_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule abi_image_unwrap_label >> strip_tac >>
  metis_tac[abi_args_label_replay_mutual]
QED

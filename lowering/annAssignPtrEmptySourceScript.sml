(* Empty source expressions keep their result across gas-observation tails. *)
Theory annAssignPtrEmptySource
Ancestors
 exprLowering stmtLowering vyperInterpreter vyperState vyperValue vyperTyping
 vyperContext vyperValueOperation list
Libs monadsyntax

Theorem eval_empty_gas_obs_ptr:
 !e cx es gs. is_empty_value_expr e ==>
 eval_expr cx e (es with gas_obs := gs) =
   (FST (eval_expr cx e es), (SND (eval_expr cx e es)) with gas_obs := gs)
Proof
 rpt gen_tac >> strip_tac >>
 Cases_on `e` >> gvs[is_empty_value_expr_def]
 >~ [`Literal ann lit`]
 >- (Cases_on `lit` >> gvs[is_empty_value_expr_def] >>
     rename1 `BytesL bs` >> Cases_on `bs` >> gvs[is_empty_value_expr_def] >>
     simp[Ntimes evaluate_def 12, evaluate_literal_def, bind_def, return_def])
 >~ [`TypeBuiltin ann tb target args`]
 >- (Cases_on `tb` >> gvs[is_empty_value_expr_def] >>
     Cases_on `args` >>
     simp[Ntimes evaluate_def 12, type_builtin_args_length_ok_def,
          type_check_def, assert_def, ignore_bind_def, bind_def, raise_def,
          return_def, evaluate_type_builtin_def, lift_sum_def, AllCaseEqs()] >>
     Cases_on `evaluate_type (get_tenv cx) target` >>
     simp[lift_sum_def, bind_def, return_def, raise_def]) >>
 rename1 `Builtin ann builtin args` >> Cases_on `builtin` >>
 gvs[is_empty_value_expr_def] >>
 rename1 `MakeArray et bd` >> Cases_on `et` >> gvs[is_empty_value_expr_def] >>
 Cases_on `args` >> gvs[is_empty_value_expr_def] >>
 simp[Ntimes evaluate_def 24, builtin_args_length_ok_def,
      type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
      get_accounts_def, evaluate_builtin_def] >>
 Cases_on `compatible_bound bd 0` >>
 Cases_on `evaluate_type (get_tenv cx) x` >>
 simp[bind_def, return_def, raise_def, lift_sum_def]
QED

Theorem eval_empty_default_gas_obs_ptr:
 is_empty_value_expr e /\
 (!tv ee. eval_expr cx e es = (INL tv,ee) ==> tv = Value (default_value tyv)) /\
 eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
 tv = Value (default_value tyv)
Proof
 strip_tac >> drule eval_empty_gas_obs_ptr >>
 disch_then (qspecl_then [`cx`,`es`,`gs`] mp_tac) >>
 Cases_on `eval_expr cx e es` >> simp[] >> strip_tac >>
 gvs[] >> metis_tac[]
QED

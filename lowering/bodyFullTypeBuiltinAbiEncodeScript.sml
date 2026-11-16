Theory bodyFullTypeBuiltinAbiEncode
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimAbiEncode
  bodyInvNoDalloca bodySimFull
  vyperContext vyperInterpreter vyperState vyperAST

Theorem abi_encode_expr_full_ok:
  !cx v11 b m typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiEncode b m) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 (AbiEncode b m) typ es)
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_full_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[bodyInvNoDallocaTheory.body_inv_no_dalloca] >>
  conj_asm2_tac
  >- suspend "value" >>
  suspend "vv"
QED

Resume abi_encode_expr_full_ok[value]:
  irule expr_sim_full_of_vv >> simp[loweringPostsTheory.post_value_type_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (TypeBuiltin v11 (AbiEncode b m) typ es)
    (es' with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >> metis_tac[]
QED

Resume abi_encode_expr_full_ok[vv]:
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH es = 1 /\ ~b`
  >- suspend "singleton" >>
  suspend "tuple"
QED

Resume abi_encode_expr_full_ok[singleton]:
  gvs[] >> Cases_on `es` >> gvs[] >> rename1 `body_exprs_full_ok cx [e]` >>
  `body_exprs_full_ok cx [e]` by
    (first_x_assum irule >> simp[type_check_def,
      vyperContextTheory.type_builtin_args_length_ok_def, assert_def]) >>
  `expr_body_pre cenv cx env e es'` by
    (irule exprSimAbiEncodeRuntimeInputsTheory.abi_encode_body_arg_pre >>
     goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es'` by
    (gvs[body_exprs_full_ok_def] >>
     qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     once_rewrite_tac[body_expr_full_ok_def] >> metis_tac[]) >>
  Cases_on `is_word_type (expr_type e)`
  >- suspend "word" >> suspend "nonword"
QED

Resume abi_encode_expr_full_ok[word]:
  FAIL_TAC "word full"
QED

Resume abi_encode_expr_full_ok[nonword]:
  FAIL_TAC "nonword full"
QED

Resume abi_encode_expr_full_ok[tuple]:
  FAIL_TAC "tuple full"
QED

Finalise abi_encode_expr_full_ok

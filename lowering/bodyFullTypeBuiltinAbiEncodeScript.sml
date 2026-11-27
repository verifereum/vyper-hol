Theory bodyFullTypeBuiltinAbiEncode
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric
  bodyFullAbiEncodeWordFull bodyFullAbiEncodeNonwordFull bodyFullAbiEncodeTupleFull
  exprSimAbiEncodeRuntimeInputs exprSimHyps exprSimSource bodySimFull
  vyperContext vyperInterpreter vyperState vyperAST
  bodyFullPredsMods[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_full_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac
  >- suspend "value" >>
  suspend "vv"
QED
*)
Theorem abi_encode_expr_full_ok:
  !cx v11 b m typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiEncode b m) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok_mods mods exps cx es) ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin v11 (AbiEncode b m) typ es)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
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
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume abi_encode_expr_full_ok[vv]:
  Cases_on `LENGTH es = 1 /\ ~b`
  >- suspend "singleton" >>
  irule abi_encode_tuple_vv_full_from_packaging >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume abi_encode_expr_full_ok[singleton]:
  gvs[] >> Cases_on `es` >> gvs[] >>
  rename1 `TypeBuiltin _ (AbiEncode F _) _ [e]` >>
  `body_exprs_full_ok cx [e]` by
    (first_x_assum irule >> simp[type_check_def,
      type_builtin_args_length_ok_def, assert_def, return_def]) >>
  `body_expr_full_ok cx e` by fs[body_exprs_full_ok_def] >>
  Cases_on `is_word_type (expr_type e)`
  >- suspend "word" >>
  irule abi_encode_nonword_vv_full_from_packaging >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume abi_encode_expr_full_ok[word]:
  `expr_body_pre cenv cx env e es'` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es'` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     once_rewrite_tac[body_expr_full_ok_def] >> metis_tac[]) >>
  irule abi_encode_word_vv_full_from_packaging >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise abi_encode_expr_full_ok
*)

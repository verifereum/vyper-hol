(*
 * Expression simulation: abi_encode.
 *
 * compile_abi_encode_case, the case lemma exprSimAggregates re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimAbiEncode
Ancestors
  exprSimHypsDefs vyperAST exprSimAbiEncodeNonwordCase
  exprSimAbiEncodeWordCase exprSimAbiEncodeTupleCase
  exprSimAbiEncodeArgs exprSimHash exprLowering vyperTypeCallGraph
  exprSimAbiEncodeRuntimeInputs exprSimProps

Theorem compile_abi_encode_case:
  !nocalls ctx func cenv cx ann ensure mid t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiEncode ensure mid) t args)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH args = 1 /\ ~ensure`
  >- (rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
      Cases_on `args` >> gvs[] >>
      rename1 `exprs_case _ _ _ _ _ [e]` >>
      `expr_body_pre cenv cx env e es` by
        (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
      `expr_sim ctx func cenv cx (expr_type e) e es` by
        (fs[exprs_case_def, expr_sim_case_def, int_calls_expr_def] >> metis_tac[]) >>
      Cases_on `is_word_type (expr_type e)`
      >- (irule compile_abi_encode_word_vv_sim >> simp[] >> qexists `env` >> simp[]) >>
      irule compile_abi_encode_nonword_vv_sim >>
      simp[] >> qexists `env` >> simp[]) >>
  irule compile_abi_encode_tuple_vv_case >> simp[] >> metis_tac[]
QED

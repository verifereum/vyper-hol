(*
 * Expression simulation: abi_decode, with its validation aborts.
 *
 * compile_abi_decode_case, the case lemma exprSimAggregates re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimAbiDecode
Ancestors
  exprSimHypsDefs exprSimDefs exprSimAbiDecodeEntryTyping exprSimUnwrap
  vyperAST exprSimHyps exprSimSource exprOpenFirstOperand
  exprSimAbiDecodeCompose exprSimAbiDecodeInputBound exprSimAbiDecodeBodyEntry
  exprSimAbiDecodeResources exprSimAbiDecodeCountedOutcome
  exprSimAbiDecodeBodySuccess exprSimAbiDecodeReject
  exprLowering exprLoweringProps loweringPosts compileEnv
  vyperTypeSystem vyperState gasOutcome gasSummary gasSummaryCompose
  fragGasPath fragGasMode fragExec exprSimAbiDecodeOblivious list

Theorem compile_abi_decode_case:
  !nocalls ctx func cenv cx ann unwrap t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiDecode unwrap) t args)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (TypeBuiltin ann (AbiDecode unwrap) t args)` by
    fs[expr_body_pre_def] >>
  drule abi_decode_parent_type >> strip_tac >> gvs[exprs_case_def] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[expr_body_pre_type_builtin_head] >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ _`
      (irule o REWRITE_RULE [expr_sim_case_def]) >>
     metis_tac[int_calls_type_builtin_arg, MEM]) >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
       Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline exprLoweringTheory.as_ptr_val_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `compile_expr cenv (BaseT (BytesT (Dynamic n))) e sa = (evv, sm)` >>
  rename1 `unwrap_value cenv evv sm = (data, start)` >>
  `lower_value compile_expr cenv (expr_type e) e sa = (data,start)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa start` by
    metis_tac[compile_expr_extends, unwrap_value_extends, cs_extends_trans] >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `start`, `data`, `s0`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          irule abi_decode_normal_prefix_summary >>
          goal_assum (drule_at Any) >> metis_tac[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      irule abi_decode_child_exit_summary >>
      qexistsl_tac [`es_end`, `y`, `r`] >> simp[] >>
      Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def] >>
      Cases_on `e'` >> gvs[expr_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule abi_decode_child_exempt_cert >> simp[]
QED

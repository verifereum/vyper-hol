(* Source and paired compiler boundaries for the joint RawRevert case. *)
Theory bodyFullRawRevertInterfaces
Ancestors
  exprSimHypsDefs exprLoweringProps builtinSystem gasShadowState gasShadow
  fragExec vyperInterpreter vyperTypeSystem supportedExprTraverse
  list rich_list pair allocLimits vyperTypeCallGraph vyperState
  exprLowering compileEnv emitHelper vyperAST exprCallbackContracts
Libs
  pairLib

Theorem raw_revert_source_pre:
  !cenv cx env ann args dflt es.
    expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
    ?e n. args = [e] /\ ann = NoneT /\ dflt = NONE /\
      expr_type e = BaseT (BytesT (Dynamic n)) /\
      (!es'. expr_sim_inv cenv cx env es' ==>
         expr_body_pre cenv cx env e es') /\
      eval_expr cx (Call ann RawRevert args dflt) =
        bind (bind (eval_expr cx e) (read_result cx))
          (\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
                    (\data. raise (Error (RevertData data))))
Proof
  rpt gen_tac >> strip_tac >>
  `?e n. args = [e] /\ ann = NoneT /\ dflt = NONE /\
           expr_type e = BaseT (BytesT (Dynamic n))` by
    gvs[expr_body_pre_def, well_typed_expr_def, LENGTH_EQ_NUM_compute] >>
  gvs[] >> conj_tac
  >- (rw[expr_body_pre_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
          alloc_limits_expr_def, int_calls_expr_def,
          expr_has_evm_run_thm, supported_expr_exists_def,
          supported_exprs_exists_every]) >>
  rw[FUN_EQ_THM] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_def, ignore_bind_def, return_def, type_check_def, assert_def,
       raise_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem raw_revert_layout_shadow:
  !cenv ty ann e dflt sa sb vv ssa ssb svv func sfunc.
    gas_shadow_compiles
      (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)) /\
    gas_shadow_state sa ssa /\
    compile_expr cenv ty (Call ann RawRevert [e] dflt) sa = (vv,sb) /\
    compile_expr cenv ty (gas_shadow_expr (Call ann RawRevert [e] dflt))
      ssa = (svv,ssb) /\
    fn_has_code sa sb func /\ fn_has_code ssa ssb sfunc ==>
    ?data sm ssm.
      vv = StackValue ann (Lit 0w) /\ svv = StackValue ann (Lit 0w) /\
      lower_value compile_expr cenv (expr_type e) e sa = (data,sm) /\
      lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
        ssa = (data,ssm) /\
      gas_shadow_state sm ssm /\
      compile_raw_revert data sm = ((),sb) /\
      compile_raw_revert data ssm = ((),ssb) /\
      ci_mono sa sm /\ ci_mono sm sb /\
      ci_mono ssa ssm /\ ci_mono ssm ssb /\
      fn_has_code sa sm func /\ fn_has_code sm sb func /\
      fn_has_code ssa ssm sfunc /\ fn_has_code ssm ssb sfunc
Proof
  rpt gen_tac >>
  simp[Once compile_expr_def, gas_shadow_expr_def] >>
  simp[Once compile_expr_def, compile_call_def, expr_type_def,
       lower_value_callback_contract, expr_child_callback_agrees] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `lower_value
      (expr_child_callback (expr_size e +
        (type_size ann + (option_size expr_size dflt + 2))) compile_expr)
      cenv (expr_type e) e = lower_value compile_expr cenv (expr_type e) e` by
    (irule lower_value_callback_contract >>
     irule expr_child_callback_agrees >> simp[]) >>
  `lower_value
      (expr_child_callback (expr_size (gas_shadow_expr e) +
        (type_size ann +
         (option_size expr_size (OPTION_MAP gas_shadow_expr dflt) + 2)))
        compile_expr) cenv (expr_type e) (gas_shadow_expr e) =
      lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)` by
    (irule lower_value_callback_contract >>
     irule expr_child_callback_agrees >> simp[]) >>
  gvs[] >>
  qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
  simp[gas_shadow_compiles_def] >>
  disch_then drule >> simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa st1` by
    (`ci_mono sa (SND (lower_value compile_expr cenv (expr_type e) e sa))`
       suffices_by gvs[] >>
     irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
  `ci_mono ssa st1'` by
    (`ci_mono ssa (SND (lower_value compile_expr cenv (expr_type e)
                        (gas_shadow_expr e) ssa))` suffices_by gvs[] >>
     irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
  `ci_mono st1 sb /\ ci_mono st1' ssb` by
    (qpat_x_assum `compile_raw_revert data st1 = _` mp_tac >>
     qpat_x_assum `compile_raw_revert data st1' = _` mp_tac >>
     simp[compile_raw_revert_def, emit_op_def, emit_inst_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def, ci_mono_def,
          cs_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC] >>
     rpt strip_tac >> gvs[] >> conj_tac >> qexists_tac `[]` >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

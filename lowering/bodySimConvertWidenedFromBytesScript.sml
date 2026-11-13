Theory bodySimConvertWidenedFromBytes
Ancestors
  bodySimConvertWidenedFacts exprSimConvertFromBytes exprSimConvert
  exprSimHyps exprSimHypsDefs exprLoweringProps exprOperandVar
  gasSummaryCompose gasExemptCert gasContext fragGasMode fragGasPath
  fragExec compileEnv exprSimSource list

Theorem intcall_convert_from_bytestring_sim:
  !ctx func cenv cx env ty ann t a fid args drv es.
    expr_body_pre cenv cx env
      (TypeBuiltin ann Convert t [Call a (IntCall fid) args drv]) es /\
    is_bytestring_type a /\ ~is_bytestring_type t /\
    expr_sim ctx func cenv cx a (Call a (IntCall fid) args drv) es ==>
    expr_sim ctx func cenv cx ty
      (TypeBuiltin ann Convert t [Call a (IntCall fid) args drv]) es
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `e1 = Call a (IntCall fid) args drv` >>
  `expr_type e1 = a` by simp[Abbr `e1`, vyperASTTheory.expr_type_def] >>
  `is_bytestring_type (expr_type e1)` by simp[] >>
  drule dynamic_convert_typing_boundary >> strip_tac >>
  drule_all dynamic_scalar_type >> strip_tac >>
  simp[exprSimDefsTheory.expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_dynamic_convert >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `dynamic_straight_fresh (compile_type_convert x (mk_convert_op (expr_type e1) t))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[] >> metis_tac[]) >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    (Cases_on `lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
               lowered_value_type cenv e1 = BaseT (StringT 0)`
     >- gvs[cs_extends_def] >>
     fs[dynamic_straight_fresh_def, dynamic_writes_fresh_def] >>
     first_x_assum drule >> strip_tac >>
     simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND3]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_sim_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "counted" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule convert_exempt_cert >> simp[]
QED

Resume intcall_convert_from_bytestring_sim[counted]:
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[eval_expr_convert_action] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
  strip_tac
  >- suspend "value" >>
  Cases_on `res` >- gvs[] >>
  simp[gasSummaryTheory.gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
  simp[] >> conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> simp[]) >>
  gvs[]
QED

Resume intcall_convert_from_bytestring_sim[value]:
  gvs[] >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e1])
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) dynamic_convert_operand_typed) >> strip_tac >>
  `~t'.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `((lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv e1 = BaseT (StringT 0)) ==> v = BytesV [] \/ v = StringV "")` by
    (strip_tac >> drule expr_body_pre_convert >> strip_tac >>
     gvs[] >> unabbrev_all_tac >>
     drule_at (Pos last) (CONV_RULE (DEPTH_CONV ETA_CONV) intcall_lowered_zero_read_empty) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >> simp[]) >>
  drule_all (Q.INST [`t` |-> `ann`] dynamic_continuation_summary
             |> SIMP_RULE (srw_ss()) []) >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`,`es_end'`,`r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`]
              gasSummaryComposeTheory.gas_marked_exec_bind_normal
              |> REWRITE_RULE [APPEND_NIL]) >>
       qexistsl_tac [`es_end`,`t'`,`v`] >> gvs[]) >>
   gvs[])
QED
Finalise intcall_convert_from_bytestring_sim

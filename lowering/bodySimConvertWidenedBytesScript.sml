Theory bodySimConvertWidenedBytes
Ancestors
  bodySimConvertWidenedFacts exprSimConvertBytes exprSimConvert
  exprSimHyps exprSimHypsDefs exprLoweringProps exprOperandVar gasSummaryCompose fragExec compileEnv
  gasExemptCert gasContext fragGasMode fragGasPath

Theorem intcall_convert_bytestring_sim:
  !ctx func cenv cx env ty ann t a fid args drv es.
    expr_body_pre cenv cx env
      (TypeBuiltin ann Convert t [Call a (IntCall fid) args drv]) es /\
    is_bytestring_type t /\
    expr_sim ctx func cenv cx a (Call a (IntCall fid) args drv) es ==>
    expr_sim ctx func cenv cx ty
      (TypeBuiltin ann Convert t [Call a (IntCall fid) args drv]) es
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rename1 `TypeBuiltin t Convert t [_]` >>
  qabbrev_tac `e1 = Call a (IntCall fid) args drv` >>
  `expr_type e1 = a` by simp[Abbr `e1`, vyperASTTheory.expr_type_def] >>
  simp[exprSimDefsTheory.expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_convert_bytestring >> strip_tac >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `is_bytestring_type (expr_type e1)` by metis_tac[valid_conversion_to_bytestring] >>
  `is_bytestring_type (lowered_value_type cenv e1)` by
    (unabbrev_all_tac >> drule ifexp_body_pre_intcall_physical >>
     metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
   s1.cs_next_id <= sb.cs_next_id` by
    (Cases_on `type_memory_bytes cenv (lowered_value_type cenv e1) < type_memory_bytes cenv t`
     >- (gvs[] >>
         `0 < type_memory_bytes cenv (lowered_value_type cenv e1)` by
           metis_tac[valueCopyBytesTheory.bytestring_memory_bytes_positive] >>
         drule_all convert_widen_copy_parts >> strip_tac >>
         `ci_mono s1 mid` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
         `ci_mono mid sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
         gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     gvs[] >> metis_tac[convert_bytestring_suffix_grows]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "counted" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule convert_exempt_cert >> simp[]
QED

Resume intcall_convert_bytestring_sim[counted]:
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[eval_expr_convert_action] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
  strip_tac
  >- suspend "normal" >>
  Cases_on `res` >- gvs[] >>
  simp[gasSummaryTheory.gas_summary_at_def] >> qexistsl_tac [`INR y`, `es_end`, `r`] >>
  simp[] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >> gvs[]
QED

Resume intcall_convert_bytestring_sim[normal]:
  gvs[] >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  suspend "typed"
QED

Resume intcall_convert_bytestring_sim[typed]:
  `expr_body_pre cenv cx env e1
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
         value_has_type tv1 v` by
    (`value_runtime_typed env (expr_type e1) v` by
       metis_tac[memory_rhs_read_annotation_typed] >>
     `env.type_defs = get_tenv cx` by
       gvs[expr_body_pre_def, expr_sim_inv_def,
           vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def] >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  `?tv2. evaluate_type (get_tenv cx) t = SOME tv2` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
      (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1)` by
    (unabbrev_all_tac >> irule intcall_bytestring_read_footprint >>
     metis_tac[vyperASTTheory.expr_type_def]) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (`MAP FDOM (es with gas_obs := gas_explicit marks s0.vs_gas_readings).scopes =
      MAP FDOM (es_end with gas_obs := []).scopes` by
       metis_tac[exprBopSimPropsTheory.bop_value_scopes_dom] >> gvs[]) >>
  suspend "compose"
QED

Resume intcall_convert_bytestring_sim[compose]:
  `~t'.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `expr_res_ok (convert_result cx (expr_type e1) t v)` by
    (qpat_x_assum
       `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     rewrite_tac[eval_expr_convert_action] >>
     simp[vyperStateTheory.bind_def] >> disch_then irule >> simp[]) >>
  `type_memory_bytes cenv t < dimword (:256)` by
    (`~is_word_type t` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
     `alloc_limits_expr cenv (TypeBuiltin t Convert t [e1])` by
       gvs[expr_body_pre_def] >>
     gvs[allocLimitsTheory.alloc_limits_expr_def,
         allocLimitsTheory.type_alloc_ok_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `~expr_has_effect (TypeBuiltin t Convert t [e1]) ==> ~expr_has_effect e1` by
    simp[loweringPostsTheory.expr_has_effect_thm] >>
  drule_all (Q.INST [`e` |-> `TypeBuiltin t Convert t [e1]`]
    convert_bytestring_continuation_summary |> REWRITE_RULE [vyperASTTheory.expr_type_def]) >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
              |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
       qexistsl_tac [`es_end`, `t'`, `v`] >> gvs[]) >>
   gvs[])
QED

Finalise intcall_convert_bytestring_sim

(* Reached source and offset operands of the linked Extract32 builtin. *)
Theory bodyExtractOperandCutsMods
Ancestors
  bodyFullPredsMods bodyExtractPrepareMods bodyExtractSuffixMods
  bodyStructFieldsSourceMods bodyAggregateArityMods exprBodyPreProps
  exprSimExtract32Source typeBuiltinPrereqs gasShadowCompileStmtHelpers
  gasShadowCompileBuiltinBytes exprSimSource vyperTypeSystem vyperValue
  vyperContext vyperAST list exprSimHypsDefs allocLimits vyperTypeCallGraph
  supportedExprTraverse constSubstCorrect vyperTypeCallStackSoundness
  gasShadowState exprLowering exprLoweringProps fragExec compileEnv context bodyFullShared

Theorem extract32_operand_shape_mods:
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 ret args) es ==>
  ?src off m k bt.
    args = [src;off] /\ expr_type src = BaseT (BytesT (Dynamic m)) /\
    expr_type off = BaseT (UintT k) /\ ann = BaseT bt /\ ret = BaseT bt /\
    extract32_result_base_ok bt /\
    (case bt of UintT n => n <= 256 | IntT n => 0 < n /\ n <= 256 |
       BytesT (Fixed n) => n <= 32 | _ => T)
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_type_builtin_args_def,
       type_builtin_result_ok_def, is_uint_type_def, LENGTH_EQ_NUM] >>
  strip_tac >> Cases_on `args` >> gvs[] >>
  rename1 `LENGTH rest = 1` >> Cases_on `rest` >> gvs[] >>
  qpat_x_assum `well_formed_type _ _` mp_tac >>
  Cases_on `bt` >>
  simp[well_formed_type_def, evaluate_type_def] >>
  rpt CASE_TAC >> gvs[] >> decide_tac
QED

Theorem extract32_operand_pre_mods:
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  expr_sim_inv_mods mods cenv cx env mid /\ (e = src \/ e = off) ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, frame_well_typed_exprs_cons] >>
  rpt strip_tac >> gvs[call_evaluation_safe_def] >> metis_tac[]
QED

Theorem extract32_paired_cuts_mods:
  compile_expr cenv ty (TypeBuiltin ann Extract32 ret [src;off]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (TypeBuiltin ann Extract32 ret [src;off])) sha = (vv,shb) /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_state sa sha ==>
  ?srcop sm shm len data sn shn offop sq shq raw sr op.
    lower_value compile_expr cenv (expr_type src) src sa = (srcop,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
      (gas_shadow_expr src) sha = (srcop,shm) /\
    compile_bytestring_src srcop sm = ((len,data),sn) /\
    lower_value compile_expr cenv ty off sn = (offop,sq) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr off) shn = (offop,shq) /\
    compile_extract32_load len data offop sq = (raw,sr) /\
    compile_clamp_basetype raw ret sr = (op,sb) /\ vv = StackValue ann op /\
    gas_shadow_state sm shm /\ gas_shadow_state sn shn /\ gas_shadow_state sq shq /\
    ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sq /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sq func /\
    fn_has_code sq sb func /\ fn_has_code sha shm shadow_func /\
    fn_has_code shn shq shadow_func
Proof
  strip_tac >>
  qpat_assum `compile_expr _ _ (TypeBuiltin _ _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP extract32_compile_equations) >>
  drule_all_then strip_assume_tac extract32_compile_cuts >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP extract32_compile_equations o
      SRULE [gasShadowTheory.gas_shadow_expr_def]) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) sha = _`
    (fn th => drule_all_then strip_assume_tac
       (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] extract32_compile_cuts) th)) >>
  fs[gasShadowTheory.gas_shadow_expr_type] >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type src) src)
    (lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
      (gas_shadow_expr src))` by irule gas_shadow_stmt_lower_value_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[] >>
  rename1 `lower_value _ cenv _ src sa = (srcop,sm)` >>
  `gas_shadow_compiles (compile_bytestring_src srcop) (compile_bytestring_src srcop)` by
    simp[gas_shadow_compiles_bytestring_src] >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[] >>
  `gas_shadow_compiles (lower_value compile_expr cenv ty off)
    (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr off))` by
    irule gas_shadow_stmt_lower_value_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[] >> metis_tac[]
QED

(* The offset IH is usable only after the actual source evaluation and read. *)
Theorem extract32_offset_source_mods:
  body_exprs_full_ok_mods mods exps cx [src;off] /\
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  body_const_cells_agree_mods mods cx env es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  bind (eval_expr cx src) (read_result cx) es = (INL v,mid) ==>
  body_expr_full_ok_mods mods exps cx off /\
  expr_body_pre_mods mods cenv cx env off mid /\
  body_const_cells_agree_mods mods cx env mid /\
  (?bs. v = BytesV bs /\ LENGTH bs <= m) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env src es` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (TypeBuiltin _ _ _ _) _`
       (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          extract32_operand_pre_mods) th)) >> simp[]) >>
  drule_all_then strip_assume_tac bodyWriteSubscriptSourceModsTheory.write_index_read_source_mods >>
  simp[] >> conj_tac
  >- (`body_exprs_full_ok_mods mods exps cx [off]` suffices_by
        simp[body_exprs_full_ok_mods_def] >>
      qpat_x_assum `body_exprs_full_ok_mods _ _ _ [src;off]` mp_tac >>
      simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
      qpat_x_assum `_ ==> body_exprs_full_ok_mods _ _ _ [off]` irule >>
      qpat_x_assum `bind _ _ es = _` mp_tac >>
      simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `expr_body_pre_mods _ _ _ _ (TypeBuiltin _ _ _ _) _`
        (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           extract32_operand_pre_mods) th)) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
      Cases_on `v` >>
      gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          evaluate_type_def, vyperTypingTheory.value_has_type_def]) >>
  qpat_assum `bind _ _ es = _` (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV)
    exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom]
QED

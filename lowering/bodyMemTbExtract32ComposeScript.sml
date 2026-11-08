(* Counted memory composition for dynamic extract32 operands. *)
Theory bodyMemTbExtract32Compose
Ancestors
  bodyMemTbExtract32Encoding bodyMemTbExtract32WordSuffix bodyDeclMemoryCompose bodyMemTbExtract32Bind bodyMemTbExtract32Action bodyMemTbExtract32TypedSuffix bodyMemoryPreds exprSimDefs
  exprSimMemoryStack exprSimSource exprSimProps exprSimMemDefs bodyMemTbExtract32Source
  exprSimDefs exprSimHypsDefs gasNormalPrefix fragGasMode fragGasPath context
  exprOperandVar fragExec rich_list bodyMemTbExtract32SnapshotEntry bodyMemTbExtract32SuffixPost
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  exprLoweringProps exprLowering compileEnv loweringPosts bodyMemTbExtract32Cuts
  exprOpenFirstOperand exprSimHypsDefs emitHelper vyperValue
  vyperInterpreter vyperState vyperTypeSystem vyperAST list
  vyperTyping vyperTypeExprResult vyperTypeInvariants vyperTypeExprSoundness
  valueEncoding integer_word venomExecSemantics venomState builtinBytes emitHelperProps

Theorem compile_extract32_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  body_exprs_mem_ok cx [src;off] /\
  expr_type src = BaseT (BytesT (Dynamic cap)) /\
  expr_type off = BaseT (UintT k) ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Extract32 ret [src;off]) es
Proof
  strip_tac >> drule extract32_body_result_type >> strip_tac >> gvs[] >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- (Cases_on `bt` >> gvs[extract32_result_base_ok_def, expr_type_def, is_word_type_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >> gvs[extract32_result_base_ok_def, is_word_type_def] >>
    fs[expr_body_pre_def, well_typed_expr_def, well_formed_type_def, evaluate_type_def]) >>
  Cases_on `compile_expr cenv ty (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) sa` >>
  rename1 `_ = (vv,sc)` >>
  drule extract32_compile_equations >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `expr_type src = _` (fn th =>
    drule_all (REWRITE_RULE [th] extract32_compile_cuts)) >> strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_head >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type src) src es` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (irule extract32_source_admissible >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `src_op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "source_summary"
  >> suspend "source_exempt"
QED

Resume compile_extract32_sim_mem[source_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
  >- suspend "source_normal"
  >> suspend "source_exception"
QED
Resume compile_extract32_sim_mem[source_normal]:
  gvs[] >>
  `bind (eval_expr cx src) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, es_end with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env src
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pos (el 2)) (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
  disch_then drule >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?bs. v = BytesV bs /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
      SOME (BaseTV (BytesT (Dynamic cap)))` by
    (gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
         evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs()]) >>
  gvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  suspend "snapshot"
QED
Resume compile_extract32_sim_mem[snapshot]:
  `!x. src_op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv s1` by
    (irule compiler_ci_mono_reserved >> qexists_tac `sa` >> simp[]) >>
  `expr_store_bound cx (expr_type src) (BytesV bs) src_op t` by simp[] >>
  `evaluate_type (get_tenv cx) (expr_type src) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by simp[] >>
  drule_all extract32_source_snapshot_entry >> strip_tac >>
  `expr_body_pre cenv cx env off (es_end with gas_obs := [])` by
    (irule extract32_offset_body_pre >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`BaseT bt`, `BaseT bt`] >> simp[]) >>
  `body_expr_mem_ok cx off` by
    (fs[body_exprs_mem_ok_def] >>
     first_x_assum irule >>
     qpat_x_assum `bind (eval_expr cx src) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx ty off (es_end with gas_obs := [])` by
    metis_tac[body_expr_mem_ok_def] >>
  suspend "offset_open"
QED
Resume compile_extract32_sim_mem[offset_open]:
  `gas_admissible (bind (eval_expr cx off) (read_result cx)) expr_res_ok
     (es_end with gas_obs := [])` by
    (qpat_x_assum `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ _`
       mp_tac >> rewrite_tac[extract32_eval_action] >>
     once_rewrite_tac[bind_assoc] >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
     Cases_on `res` >- simp[expr_res_ok_def] >>
     first_x_assum (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     simp[Once bind_def] >> simp[Once bind_def] >>
     simp[Once bind_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ off _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `off_op`, `u`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "offset_summary"
  >> suspend "offset_exempt"
QED
Resume compile_extract32_sim_mem[offset_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
  >- suspend "offset_normal"
  >> suspend "offset_exception"
QED
Resume compile_extract32_sim_mem[offset_exception]:
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end'`, `r`] >> simp[] >>
  rewrite_tac[extract32_eval_action] >> once_rewrite_tac[bind_assoc] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  irule gas_marked_exec_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[] >> once_rewrite_tac[bind_assoc] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume compile_extract32_sim_mem[offset_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[extract32_eval_action] >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec T _ source _ _ _ _ _` >>
  qmatch_asmsub_abbrev_tac `ignore_bind offset (return ())` >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >>
  irule gas_exempt_cert_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[bind_assoc] >> irule gas_exempt_cert_error_value >> simp[]
QED
Resume compile_extract32_sim_mem[source_exception]:
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
  rewrite_tac[extract32_eval_action] >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec T _ source _ _ _ _ _` >>
  rewrite_tac[bind_assoc] >> simp[] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume compile_extract32_sim_mem[source_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[extract32_eval_action] >>
  qmatch_asmsub_abbrev_tac `ignore_bind source (return ())` >>
  rewrite_tac[ignore_bind_def, bind_assoc] >> simp[] >>
  irule gas_exempt_cert_error_value >> simp[]
QED
Resume compile_extract32_sim_mem[offset_normal]:
  gvs[] >>
  `b < dimword (:256)` by decide_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) b t'.vs_memory` by
    (`expr_sim_inv cenv cx env (es_end with gas_obs := [])` by simp[] >>
     `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
        (w2n (n2w b:bytes32)) u.vs_memory` by simp[wordsTheory.w2n_n2w] >>
     drule_all extract32_source_bytes_kept >> simp[wordsTheory.w2n_n2w]) >>
  `bind (eval_expr cx off) (read_result cx)
    (es_end with gas_obs := gas_explicit marks' u.vs_gas_readings) =
    (INL v, es_end' with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ marks' _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env off
    (es_end with gas_obs := gas_explicit marks' u.vs_gas_readings)` by simp[] >>
  drule_at (Pos (el 2)) (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
  disch_then drule >> strip_tac >>
  `?i. v = IntV i /\ 0 <= i /\ i < &dimword (:256)` by
    (gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
         evaluate_type_def] >> Cases_on `v` >>
     gvs[value_has_type_def, AllCaseEqs()] >>
     `Num i < (2:num) ** 256` by
       (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >> simp[]) >>
     fs[wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
  gvs[] >> suspend "suffix_entry"
QED
Resume compile_extract32_sim_mem[suffix_entry]:
  `~(i < 0)` by intLib.ARITH_TAC >>
  `post_value_type cenv off = expr_type off` by
    (irule post_value_type_word >>
     qpat_assum `expr_type off = BaseT _` (fn th => simp[th, is_word_type_def])) >>
  `eval_operand off_op t' = SOME (n2w (Num i))` by
    (qpat_assum `expr_post _ _ _ _ off _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
         value_has_type_def, expr_val_rel_def, is_word_type_def, evaluate_type_def,
         typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_def]) >>
  `?ln dn. len = Var ln /\ data = Var dn` by
    (qpat_x_assum `compile_bytestring_src _ _ = _` mp_tac >>
     Cases_on `emit_op MLOAD [src_op] s1` >>
     rename1 `_ = (lp, sl)` >>
     Cases_on `emit_op ADD [src_op; Lit 32w] sl` >>
     simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
     rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> gvs[]) >>
  `!opr. (opr = len \/ opr = data) ==> eval_operand opr t' = eval_operand opr u` by
    (qpat_assum `expr_post _ _ _ _ off _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     rpt strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand len t' = SOME (n2w (LENGTH bs)) /\
   eval_operand data t' = SOME (n2w (b + 32))` by simp[] >>
  `b + 32 + LENGTH bs <= t'.vs_alloca_next` by decide_tac >>
  `local_ptrs_reserved cenv s3` by
    (irule compiler_ci_mono_reserved >> qexists_tac `s2` >> simp[]) >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `!x. len = Var x \/ data = Var x \/ off_op = Var x ==> not_fresh_at s3 x` by
    (`!x. off_op = Var x ==> not_fresh_at s3 x` by
       metis_tac[compile_lower_value_var] >>
     rpt strip_tac >> gvs[] >>
     irule compiler_ci_mono_not_fresh >> qexists_tac `s2` >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_assum `bind (eval_expr cx src) _ _ = _`
       (mp_tac o MATCH_MP (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `wb_frame cenv es sa s0 t'` by
    (irule extract32_operands_frame >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any)) >>
  `well_formed_type (get_tenv cx) (BaseT bt)` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  `Num i < dimword (:256)` by
    (simp[integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC) >>
  `alloca_room ctx func t'` by fs[expr_post_def, stmt_state_rel_def] >>
  `t'.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt] >>
  `Num i + 32 <= LENGTH bs ==> b + 32 + Num i < dimword (:256)` by decide_tac >>
  Cases_on `evaluate_extract32 bs (Num i) bt`
  >- suspend "suffix_success"
  >> suspend "suffix_revert"
QED
Resume compile_extract32_sim_mem[suffix_success]:
  `Num i + 32 <= LENGTH bs` by
    (fs[vyperContextTheory.evaluate_extract32_def, AllCaseEqs()]) >>
  `stmt_state_rel ctx func cenv cx es_end' t'` by fs[expr_post_def] >>
  `is_word_type (BaseT bt)` by
    (Cases_on `bt` >> gvs[extract32_result_base_ok_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[extract32_result_base_ok_def, is_word_type_def] >>
     fs[well_formed_type_def, evaluate_type_def]) >>
  `sa.cs_next_var <= s3.cs_next_var` by fs[ci_mono_def] >>
  `b + 32 + Num i < dimword (:256)` by simp[] >>
  drule_all extract32_word_suffix_success >>
  disch_then (qspecl_then [`src`, `off`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func t' ng (OK u')` >>
  `s0.vs_alloca_next <= u'.vs_alloca_next` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = t` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >> decide_tac) >>
  qexists_tac `marks ++ (marks' ++ REPLICATE ng F)` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL x`, `es_end'`, `OK u'`] >> simp[] >>
  reverse conj_tac >-
    (qpat_x_assum `expr_post _ _ _ _ (TypeBuiltin _ _ _ _) _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_at_def, expr_type_def] >>
     strip_tac >> simp[] >> metis_tac[]) >>
  rewrite_tac[extract32_eval_action] >> once_rewrite_tac[bind_assoc] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  irule gas_marked_exec_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[] >> once_rewrite_tac[bind_assoc] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  simp[gas_marked_exec_def, gas_marked_path_def,
       vyperContextTheory.evaluate_type_builtin_def,
       lift_sum_def, bind_def, return_def, raise_def, read_result_def]
QED
Resume compile_extract32_sim_mem[suffix_revert]:
  `?msg. y = RuntimeError msg` by
    (qpat_x_assum `evaluate_extract32 _ _ _ = INR y` mp_tac >>
     Cases_on `Num i + 32 <= LENGTH bs`
     >- (drule extract32_inbounds_slice >> strip_tac >> simp[] >>
         Cases_on `bt` >> fs[extract32_result_base_ok_def] >>
         simp[extract32_slice_guards, AllCaseEqs()] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         fs[extract32_result_base_ok_def] >>
         simp[extract32_slice_guards, AllCaseEqs()]) >>
     simp[vyperContextTheory.evaluate_extract32_def]) >>
  qpat_x_assum `y = RuntimeError _` SUBST_ALL_TAC >>
  drule_all extract32_word_suffix_revert >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `marks ++ (marks' ++ REPLICATE k' F)` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `es_end'`,
    `Abort Revert_abort (t'' with vs_inst_idx := j)`] >>
  simp[expr_exit_def, exit_result_def] >>
  rewrite_tac[extract32_eval_action] >> once_rewrite_tac[bind_assoc] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  irule gas_marked_exec_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[] >> once_rewrite_tac[bind_assoc] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  simp[gas_marked_exec_def, gas_marked_path_def,
       vyperContextTheory.evaluate_type_builtin_def,
       lift_sum_def, bind_def, return_def, raise_def, read_result_def]
QED
Finalise compile_extract32_sim_mem

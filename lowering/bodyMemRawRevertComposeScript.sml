(* Operand memory simulation followed by the aborting raw_revert suffix. *)
Theory bodyMemRawRevertCompose
Ancestors
  bodyMemRawRevertSuffix bodyMemRawRevertBounds exprSimRawRevertCore exprSimMemDefs
  exprSimSource exprSimHypsDefs exprSimHyps exprSimDefs loweringPosts
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragExec exprLoweringProps exprLowering
  exprOperandVar compileEnv vyperAST vyperInterpreter vyperState
  vyperTypeSystem vyperTyping vyperValue vyperContext
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants words list

Theorem raw_revert_vv_sim_mem:
  expr_body_pre cenv cx env (Call ann RawRevert [e] dflt) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Call ann RawRevert [e] dflt) es
Proof
  strip_tac >>
  `?cap. expr_type e = BaseT (BytesT (Dynamic cap))` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule raw_revert_pre_arg >> simp[] >> metis_tac[]) >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule raw_revert_compile >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[raw_revert_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `!v. data = Var v ==> not_fresh_at sm v` by
    metis_tac[compile_lower_value_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR y`, `ee`] mp_tac) >>
     simp[eval_raw_revert_action] >>
     qpat_x_assum `bind _ _ _ = _` (fn th => simp[Once bind_def, th]) >>
     simp[expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `data`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_raw_revert_action] >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[] >- suspend "success" >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_raw_revert_action, ignore_bind_bind_unit] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Resume raw_revert_vv_sim_mem[success]:
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pos (el 2))
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  disch_then drule >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `?bs. v = BytesV bs` by
    (gvs[expr_result_typed_def, expr_runtime_typed_def,
         value_result_typed_def, evaluate_type_def] >>
     Cases_on `v` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by
    gvs[expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, evaluate_type_def] >>
  drule_at (Pos hd) raw_revert_dynamic_post_bounds >> simp[] >> strip_tac >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `w2n (n2w b + 32w : 256 word) + LENGTH bs <= t.vs_alloca_next` by
    (simp[word_add_n2w, w2n_n2w] >> fs[]) >>
  `b < dimword (:256)` by decide_tac >>
  `?w. gas_path_mem ctx func t 0 (Abort Revert_abort w)` by
    (irule raw_revert_tail_path_mem >>
     simp[Once CONJ_COMM] >>
     qexistsl_tac [`data`, `LENGTH bs`, `n2w b`, `sb`, `sm`] >>
     simp[w2n_n2w]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "raw_revert"))`, `es_end`,
                `Abort Revert_abort w`] >>
  simp[exit_result_def, expr_exit_def] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl_tac [`es_end`, `t`, `BytesV bs`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def, raise_def]
QED

Resume raw_revert_vv_sim_mem[exception]:
  Cases_on `res` >> gvs[expr_exit_def] >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  Cases_on `r` >> Cases_on `y` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Finalise raw_revert_vv_sim_mem

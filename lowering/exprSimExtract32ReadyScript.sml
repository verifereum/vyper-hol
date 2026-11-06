(* Conditional assembly: dynamic bytes source and unsigned offset only. *)
Theory exprSimExtract32Ready
Ancestors
  exprSimExtract32Tail exprSimExtract32Source exprSimExtract32Counted
  exprSimExtract32ReadyFacts exprSimExtract32TailBoundary exprBopSimProps
  exprSimExtract32Lift exprSimExtract32TailLift exprOperandVar gasSummaryCompose gasSummary fragGasMode fragGasPath
  exprSimExtract32Post exprSimExtract32Assembly exprSimHypsDefs exprSimDefs
  exprLowering exprLoweringProps builtinBytes compileEnv vyperAST fragExec
  vyperState vyperTypeSystem vyperTypeCallGraph list loweringPosts vyperInterpreter vyperValue exprSimHyps

Theorem compile_extract32_ready_sim:
  exprs_case nocalls ctx func cenv cx [src;off] /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 t [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  expr_type off = BaseT (UintT k) /\
  (nocalls ==> int_calls_expr (TypeBuiltin ann Extract32 t [src;off]) = []) ==>
  expr_vv_sim ctx func cenv cx ty (TypeBuiltin ann Extract32 t [src;off]) es
Proof
  strip_tac >>
  `?bt. t = BaseT bt /\ extract32_result_base_ok bt /\ ann = t` by
    metis_tac[extract32_body_pre_shape] >> gvs[] >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[compile_extract32_stages] >>
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Dynamic m))) src sa` >>
  rename1 `_ = (src_op,st1)` >> simp[] >>
  Cases_on `compile_bytestring_src src_op st1` >>
  PairCases_on `q` >> rename1 `_ = ((len,dp),st2)` >> simp[] >>
  Cases_on `lower_value compile_expr cenv ty off st2` >>
  rename1 `_ = (off_op,st3)` >> simp[] >>
  Cases_on `compile_extract32_load len dp off_op st3` >>
  rename1 `_ = (raw,st4)` >> simp[] >>
  Cases_on `compile_clamp_basetype raw (BaseT bt) st4` >>
  rename1 `_ = (op,st5)` >>
  simp[as_stack_val_def, comp_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  `lower_value compile_expr cenv (expr_type src) src sa = (src_op,st1)` by simp[] >>
  drule_all extract32_stage_cuts >> strip_tac >>
  `expr_sim_case nocalls ctx func cenv cx src` by gvs[exprs_case_def] >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_arg >> conj_tac
     >- gvs[expr_body_pre_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `nocalls ==> int_calls_expr src = []` by
    gvs[int_calls_expr_def] >>
  `expr_sim ctx func cenv cx (expr_type src) src es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ _` mp_tac >>
     simp[expr_sim_case_def] >> disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    metis_tac[extract32_vv_first_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule_all >> strip_tac >>
  once_rewrite_tac[eval_expr_extract32_vv_bind] >>
  irule extract32_outcome_bind_marked >>
  qexists_tac `\v ee t. expr_post ctx func cenv cx src es sa st1 s0 ee v src_op t /\
     t.vs_current_bb = st1.cs_current_bb /\
     t.vs_inst_idx = LENGTH st1.cs_current_insts` >>
  reverse conj_tac
  >- (`(\(res:value+exception) (ee:evaluation_state) r.
          ?exc. res = INR exc /\ expr_exit (INR exc : eval_result+exception) r) =
        (\res ee r. expr_exit res r)` by
        (simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res`
         >- simp[] >>
         rename1 `INR exc` >>
         qspecl_then [`Value`, `INR exc`] mp_tac expr_exit_success_map >>
         simp[FUN_EQ_THM]) >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> fs[] >>
  drule_all extract32_marked_source_typed >> strip_tac >> gvs[] >>
  `expr_sim_case nocalls ctx func cenv cx off` by
    (drule_all extract32_marked_off_case >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type src) =
     SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_body_pre _ _ _ src es` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `!z. src_op = Var z ==> not_fresh_at st1 z` by
    metis_tac[compile_lower_value_var] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     drule gas_marked_path_exec >> metis_tac[gas_path_normal]) >>
  drule_all extract32_prepare_counted_arbitrary >>
  disch_then (qx_choose_then `u` (qx_choose_then `p` strip_assume_tac)) >>
  irule extract32_outcome_return_prefix >>
  simp[] >> qexistsl_tac [`u`,`BytesV bs`] >> simp[] >>
  `nocalls ==> int_calls_expr off = []` by gvs[int_calls_expr_def] >>
  `expr_sim ctx func cenv cx ty off ee` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ off` mp_tac >>
     simp[expr_sim_case_def] >> disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `gas_admissible (bind (eval_expr cx off) (read_result cx)) expr_res_ok ee` by
    (drule_all extract32_vv_second_admissible >> simp[] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee u` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ st2 _ _ _ _ u`
       (mp_tac o cj 1 o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ off _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule_all >> strip_tac >>
  irule extract32_outcome_bind_marked >>
  qexists_tac `\v ee' t. expr_post ctx func cenv cx off ee st2 st3 u ee' v off_op t /\
    t.vs_current_bb = st3.cs_current_bb /\ t.vs_inst_idx = LENGTH st3.cs_current_insts` >>
  reverse conj_tac
  >- (`(\(res:value+exception) (ee:evaluation_state) r.
          ?exc. res = INR exc /\ expr_exit (INR exc : eval_result+exception) r) =
        (\res ee r. expr_exit res r)` by
        (simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res`
         >- simp[] >> rename1 `INR exc` >>
         qspecl_then [`Value`, `INR exc`] mp_tac expr_exit_success_map >> simp[FUN_EQ_THM]) >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> fs[] >>
  `expr_body_pre cenv cx env off
      (ee with gas_obs := gas_explicit marks' u.vs_gas_readings)` by simp[] >>
  `ee' with gas_obs := [] = ee'` by simp[evaluation_state_component_equality] >>
  `(do r <- eval_expr cx off; read_result cx r od)
      (ee with gas_obs := gas_explicit marks' u.vs_gas_readings) = (INL v,ee')` by
    (qpat_assum `gas_marked_exec _ _ _ (ee,u) _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `?i. v = IntV i /\ 0 <= i` by
    (irule extract32_offset_value >> goal_assum (drule_at Any) >>
     simp[is_uint_type_def] >> metis_tac[]) >> gvs[] >>
  `Num i < dimword (:256)` by
    (irule (cj 2 extract32_offset_bounds) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_bytestring_src _ _ = _`
    (mp_tac o REWRITE_RULE [compile_bytestring_src_def, comp_bind_def, comp_return_def]) >>
  simp[LET_THM] >> pairarg_tac >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[LET_THM, comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src_op] st1 = (len,sy)` >>
  `expr_body_pre cenv cx env off
      (ee with gas_obs := gas_explicit marks' u.vs_gas_readings)` by simp[] >>
  `expr_post ctx func cenv cx src es sa cs'' s0
      (ee with gas_obs := gas_explicit marks' u.vs_gas_readings) (BytesV bs) src_op u` by
    simp[extract32_expr_post_end_gas_obs] >>
  `expr_post ctx func cenv cx off
      (ee with gas_obs := gas_explicit marks' u.vs_gas_readings)
      cs'' st3 u ee' (IntV i) off_op t'` by
    simp[extract32_expr_post_start_gas_obs] >>
  `LENGTH bs < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256)` by decide_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p t'.vs_memory /\
   eval_operand len t' = SOME (n2w (LENGTH bs)) /\
   eval_operand dp t' = SOME (n2w (p+32)) /\
   eval_operand src_op t' = SOME (n2w p) /\
   eval_operand off_op t' = SOME (n2w (Num i))` by
    (irule extract32_compiled_offset_post_view >>
     goal_assum (drule_at Any) >>
     simp[extract32_expr_post_start_gas_obs, extract32_expr_post_end_gas_obs] >>
     metis_tac[]) >>
  drule_all extract32_tail_available >> strip_tac >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ (ee,u) _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     drule gas_marked_path_exec >> metis_tac[gas_path_normal]) >>
  `evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt)` by
    metis_tac[extract32_ready_result_evaluates] >>
  `is_word_type (BaseT bt)` by metis_tac[extract32_ready_result_word] >>
  `(case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
              BytesT (Fixed k) => k <= 32 | _ => T)` by
    metis_tac[extract32_ready_result_width] >>
  `sa.cs_next_id <= cs''.cs_next_id` by
    (irule extract32_ready_prepared_id >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `sa.cs_next_var <= cs''.cs_next_var` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `gas_marked_exec _ _ _ (es,s0) _ _ _ _`
      (mp_tac o MATCH_MP bop_marked_scopes_dom) >> simp[]) >>
  `fn_has_code st3 sb func` by
    (irule (cj 2 fn_has_code_split) >>
     conj_tac >- metis_tac[cs_extends_trans] >>
     qexists_tac `sa` >> simp[] >> metis_tac[cs_extends_trans]) >>
  qpat_assum `expr_type src = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `expr_type off = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule extract32_tail_ready_any_post >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`dp`, `ee with gas_obs := gas_explicit marks' u.vs_gas_readings`,
                `len`, `m`, `off_op`, `p`, `raw`, `u`, `cs''`, `src_op`, `st4`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]
QED

(* Conditional assembly: dynamic bytes source and unsigned offset only. *)
Theory exprSimExtract32Ready
Ancestors
  exprSimExtract32Tail exprSimExtract32Source exprSimExtract32Counted
  exprSimExtract32ReadyFacts exprSimExtract32TailBoundary exprBopSimProps
  exprSimExtract32Lift exprSimExtract32TailLift exprOperandVar gasSummaryCompose gasSummary fragGasMode fragGasPath
  exprSimExtract32Post exprSimExtract32Assembly exprSimHypsDefs exprSimDefs
  exprLowering exprLoweringProps builtinBytes compileEnv vyperAST fragExec
  vyperState vyperTypeSystem vyperTypeCallGraph list loweringPosts vyperInterpreter vyperValue exprSimHyps
  gasStorage vyperStorageTrace vyperStorageFootprint

Theorem extract32_prepare_counted_horizons[local]:
  (!H. valid_horizon cx st0 H tr ==>
     expr_post H ctx func cenv cx src es sa sm s0 es' (BytesV bs) op s) /\
  valid_horizon cx st0 H0 tr /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  compile_bytestring_src op sm = ((len,dp),sb) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u p. gas_marked_exec F (ctx,func) (return (BytesV bs)) (es',s) []
          (INL (BytesV bs)) es' (OK u) /\
    (!H. valid_horizon cx st0 H tr ==>
       expr_post H ctx func cenv cx src es sa sb s0 es' (BytesV bs) op u) /\
    eval_operand op u = SOME (n2w p) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand dp u = SOME (n2w (p+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p u.vs_memory /\
    LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `post_value_type cenv src = expr_type src` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then assume_tac) >>
  drule_all extract32_prepare_post_arbitrary >>
  disch_then (qx_choose_then `u` (qx_choose_then `p` strip_assume_tac)) >>
  drule_all extract32_prepare_run_path >> strip_tac >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`p`] >>
  simp[] >>
  conj_tac
  >- simp[gas_marked_exec_def, vyperStateTheory.return_def] >>
  qx_gen_tac `H1` >> strip_tac >>
  qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ sm _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ sb _ _ _ _ _` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H1` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all extract32_prepare_post_arbitrary >>
  disch_then (qx_choose_then `u1` (qx_choose_then `p1` strip_assume_tac)) >>
  `u1 = u` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `expr_post H1 _ _ _ _ _ _ _ sb _ _ _ _ u` mp_tac >>
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, lookup_var_def, local_region_def, locals_kept_def,
       popped_kept_def] >>
  strip_tac >> simp[] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

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
  match_mp_tac extract32_outcome_bind_marked >>
  qexists_tac `\H v ee t. expr_post H ctx func cenv cx src es sa st1 s0 ee v src_op t /\
     t.vs_current_bb = st1.cs_current_bb /\
     t.vs_inst_idx = LENGTH st1.cs_current_insts` >>
  conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ _ _ (bind (eval_expr cx src) _) _ _ _` mp_tac >>
      `!(res:value+exception) r.
         (?exc. res = INR exc /\ expr_exit (INR exc : eval_result+exception) r) <=>
         expr_exit res r` by
        (rpt gen_tac >> Cases_on `res`
         >- simp[] >>
         rename1 `INR exc` >>
         qspecl_then [`Value`, `INR exc`] mp_tac expr_exit_success_map >>
         simp[FUN_EQ_THM]) >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >> asm_rewrite_tac[ETA_AX]) >>
  reverse conj_tac
  >- (gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_lifts,
           storage_trace_frame_return]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qpat_x_assum `?H. valid_horizon _ _ H ee.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  `t.vs_current_bb = st1.cs_current_bb` by
    (qpat_x_assum `!H. _ ==> t.vs_current_bb = _` (drule_then ACCEPT_TAC)) >>
  `t.vs_inst_idx = LENGTH st1.cs_current_insts` by
    (qpat_x_assum `!H. _ ==> t.vs_inst_idx = _` (drule_then ACCEPT_TAC)) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
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
  drule_all extract32_prepare_counted_horizons >>
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
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ src _ _ st2 _ _ _ _ u`
       drule >>
     simp[expr_post_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ off _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule_all >> strip_tac >>
  match_mp_tac extract32_outcome_bind_marked >>
  qexists_tac `\H v ee' t. expr_post H ctx func cenv cx off ee st2 st3 u ee' v off_op t /\
    t.vs_current_bb = st3.cs_current_bb /\ t.vs_inst_idx = LENGTH st3.cs_current_insts` >>
  conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ _ _ (bind (eval_expr cx off) _) _ _ _` mp_tac >>
      `!(res:value+exception) r.
         (?exc. res = INR exc /\ expr_exit (INR exc : eval_result+exception) r) <=>
         expr_exit res r` by
        (rpt gen_tac >> Cases_on `res`
         >- simp[] >>
         rename1 `INR exc` >>
         qspecl_then [`Value`, `INR exc`] mp_tac expr_exit_success_map >>
         simp[FUN_EQ_THM]) >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >> asm_rewrite_tac[ETA_AX]) >>
  reverse conj_tac
  >- (gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_lifts,
           storage_trace_frame_return]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee'.storage_trace ==> _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qpat_x_assum `?H. valid_horizon _ _ H ee'.storage_trace`
    (qx_choose_then `H1` assume_tac) >>
  `t'.vs_current_bb = st3.cs_current_bb` by
    (qpat_x_assum `!H. _ ==> t'.vs_current_bb = _` (drule_then ACCEPT_TAC)) >>
  `t'.vs_inst_idx = LENGTH st3.cs_current_insts` by
    (qpat_x_assum `!H. _ ==> t'.vs_inst_idx = _` (drule_then ACCEPT_TAC)) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
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
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
     expr_post H ctx func cenv cx src es sa cs'' s0
       (ee with gas_obs := gas_explicit marks' u.vs_gas_readings) (BytesV bs) src_op u /\
     expr_post H ctx func cenv cx off
       (ee with gas_obs := gas_explicit marks' u.vs_gas_readings)
       cs'' st3 u ee' (IntV i) off_op t' /\
     stmt_state_rel H ctx func cenv cx es s0` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by
       (qpat_assum `(do r <- eval_expr cx off; read_result cx r od) _ = _`
          (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
        strip_tac >>
        qpat_x_assum `valid_horizon _ _ H ee'.storage_trace` mp_tac >>
        simp[valid_horizon_def]) >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `gas_marked_exec _ _ _ (es,s0) _ _ _ _`
          (mp_tac o Q.SPEC `[]` o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
        strip_tac >>
        drule_at (Pos last) storage_trace_frame_prefix >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
        strip_tac >>
        qpat_x_assum `valid_horizon _ _ H ee.storage_trace` mp_tac >>
        simp[valid_horizon_def]) >>
     simp[extract32_expr_post_end_gas_obs, extract32_expr_post_start_gas_obs]) >>
  qpat_assum `!H. valid_horizon _ _ H ee'.storage_trace ==>
                expr_post _ _ _ _ _ src _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
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

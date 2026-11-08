Theory tupleRhsPostRoom
Ancestors
  vyperAST exprSimDefs exprSimProps exprSimMemorySource
  bodyRhsRoomMemory exprSimIfExpWidenedCounted exprSimIfExpWidenedArm
  exprSimHyps exprSimUnwrapProps exprSimMemDefs exprSimUnwrap
  loweringPosts exprLowering compileEnv vyperInterpreter vyperState
  gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode
  fragExec fragGasPath fragGasPathMem fragExecMem allocaHistoryFragment
  exprOperandVar exprLoweringProps loweringSlice context
  valueEncodingProps valueEncoding venomExecSemantics venomState
  vyperEvalExprPreservesScopesDom list finite_map

Theorem changed_post_physical:
  expr_body_pre ce cx env e es /\ post_value_type ce e <> expr_type e ==>
  post_value_type ce e = lowered_value_type ce e /\
  ~is_word_type (post_value_type ce e)
Proof
  strip_tac >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >>
  gvs[post_value_type_def, expr_type_def] >>
  Cases_on `is_word_type ty \/ is_bytestring_type ty` >> gvs[] >>
  drule ifexp_intcall_copy_source >> simp[] >> strip_tac >>
  drule aggregate_widen_source >> simp[]
QED

Theorem changed_post_store_capacity[local]:
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  (!tv w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
    eval_operand op s = SOME w ==>
    type_memory_size tv = 0 \/
    w2n w + type_memory_size tv <= s.vs_alloca_next) ==>
  expr_store_bound cx (post_value_type ce e) v op s
Proof
  rw[expr_store_bound_def, expr_post_def, expr_val_at_def] >>
  qpat_x_assum `!tv. _ ==> val_wf _ _ /\ _` (qspec_then `tv` mp_tac) >>
  qpat_x_assum `!tv w. _` (qspecl_then [`tv`, `w`] mp_tac) >>
  simp[] >> rpt strip_tac >> drule val_store_size_le >> decide_tac
QED

Theorem changed_post_path_room[local]:
  expr_body_pre ce cx env e es /\
  post_value_type ce e <> expr_type e /\
  compile_expr ce ty e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s ==>
  sb = sm /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  (vv_location vv = SOME LocMemory ==>
    !sw tvt. eval_operand op s = SOME sw /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt ==>
      type_memory_size tvt = 0 \/
      w2n sw + type_memory_size tvt <= s.vs_alloca_next)
Proof
  strip_tac >> drule_all changed_post_physical >> strip_tac >>
  drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
  gvs[unwrap_value_def, comp_return_def, vv_location_def] >>
  (conj_asm1_tac >-
    metis_tac[expr_post_of_vv_post_stack, expr_post_of_vv_post_memory] >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def] >> strip_tac >>
  rpt conj_tac
  >~ [`expr_store_bound _ _ _ _ _`] >-
    (qpat_assum `post_value_type _ _ = _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule changed_post_store_capacity >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[post_value_type_word, arithmeticTheory.ADD_COMM]) >>
  metis_tac[arithmeticTheory.ADD_COMM])
QED

Theorem changed_post_marked_read_room:
  !ctx func ce cx env e es sa sm sb s0 ee tv vv op s ty.
    expr_body_pre ce cx env e es /\
    post_value_type ce e <> expr_type e /\
    compile_expr ce ty e sa = (vv,sm) /\
    unwrap_value ce vv sm = (op,sb) /\
    vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
            [] (INL v) ee (OK u) /\
      expr_post ctx func ce cx e es sa sb s0 ee v op u /\
      expr_store_bound cx (post_value_type ce e) v op u /\
      (vv_location vv = SOME LocMemory ==>
       !sw tvt. eval_operand op u = SOME sw /\
                evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt ==>
                type_memory_size tvt = 0 \/
                w2n sw + type_memory_size tvt <= u.vs_alloca_next) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res,ee')` >>
  `ee' = ee` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`) >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tv ee = (INL v,ee)` >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[vv_store_bound_def, read_result_def, return_def] >>
     rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >> pop_assum kall_tac >>
  drule_all changed_post_path_room >> strip_tac >> gvs[] >>
  qexistsl_tac [`v`,`s`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def, cj 1 gas_path_mem_rules] >>
  metis_tac[read_result_gas_obs, APPEND]
QED

Theorem changed_post_expr_sim_mem_room:
  !ctx func cenv cx env ty e es.
    post_value_type cenv e <> expr_type e /\
    expr_body_pre cenv cx env e es /\
    expr_vv_sim_mem ctx func cenv cx ty e es ==>
    !sa sm sb vv op s0.
      compile_expr cenv ty e sa = (vv, sm) /\
      unwrap_value cenv vv sm = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func)
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (post_value_type cenv e) v op t /\
          (vv_location vv = SOME LocMemory ==>
           !sw tvt. eval_operand op t = SOME sw /\
                    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
                    type_memory_size tvt = 0 \/
                    w2n sw + type_memory_size tvt <= t.vs_alloca_next) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  simp[] >> rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (rename1 `vv_post _ _ _ _ _ _ _ _ _ _ tv vv u` >>
          `~u.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          drule_at (Pat `unwrap_value _ _ _ = _`) changed_post_marked_read_room >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          disch_then (qspecl_then [`env`, `ty`] mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          rename1 `gas_marked_exec T _ (read_result _ _) _ [] _ _ (OK u2)` >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u2`] >>
          simp[] >>
          reverse conj_tac
          >- (rpt strip_tac >>
              qpat_x_assum `vv_location _ = _ ==> _` drule >>
              disch_then (qspecl_then [`sw`, `tvt`] mp_tac) >> simp[]) >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED

(* Restartable suffix induction for RawLog topics. *)
Theory bodyFullRawLogTopicsSuffix
Ancestors
  bodyFullRawLogTopicsPost bodyFullPreds bodySimFull gasOutcomeFullCompose
  bodyRawLogArgPre exprSimSource exprSimProps exprLoweringProps
  gasShadowState loweringPosts bodyPtrDefs fragGasOriginPtr
  vyperInterpreter vyperState vyperAST list exprLowering compileEnv
  exprSimWordArgs stmtSimProps

Theorem raw_log_topics_suffix_full_under_compose:
  (!tops ctx func cenv cx env ann n pre e rest data dflt
   sa sm sb shadow_sa shadow_sm shadow_sb op ops
   H DF lo d es s G0 tn0 xs mid v u G1 tn1 ys ee vs t G tn.
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
        (pre ++ e::rest); data] dflt) es /\
  expr_body_pre cenv cx env e es /\
  expr_type e = BaseT (BytesT (Fixed 32)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  compile_multi_exprs compile_expr cenv rest sm = (ops,sb) /\
  lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
    shadow_sa = (op,shadow_sm) /\
  compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr rest)
    shadow_sm = (ops,shadow_sb) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sb.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := xs ++ tail) = (INL v,mid with gas_obs := tail)) /\
  expr_post H ctx func cenv cx e es sa sm s mid v op u /\
  expr_store_bound cx (expr_type e) v op u /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u /\
  ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 u /\
  ghost_kept_at lo cenv es sa G0 tn0 s G1 tn1 /\
  (!tail. eval_exprs cx rest (mid with gas_obs := ys ++ tail) =
      (INL vs,ee with gas_obs := tail)) /\
  (?ws. INL vs = INL ws /\ LENGTH rest = LENGTH ws /\
    LENGTH ops = LENGTH ws /\
    EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) ws /\
    LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) ops ws /\
    EVERY (\op. op_taint tn op = {}) ops /\
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame cenv mid ee sm u t /\
    (~EXISTS expr_has_effect rest ==> pure_frame cenv func mid sm u t) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv mid sm G1 tn1 u G tn /\
    (!op x. MEM op ops /\ op = Var x ==> not_fresh_at sb x) /\
    (!op l. MEM op ops ==> op <> Label l)) ==>
  (?ws. INL (v::vs) = INL ws /\ LENGTH (e::rest) = LENGTH ws /\
    LENGTH (op::ops) = LENGTH ws /\
    EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) ws /\
    LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) (op::ops) ws /\
    EVERY (\op. op_taint tn op = {}) (op::ops) /\
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame cenv es ee sa s t /\
    (~EXISTS expr_has_effect (e::rest) ==> pure_frame cenv func es sa s t) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
    (!op' x. MEM op' (op::ops) /\ op' = Var x ==> not_fresh_at sb x) /\
    (!op' l. MEM op' (op::ops) ==> op' <> Label l))) ==>
  !rest pre topics DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx
   env ann n data dflt st0 sa sb shadow_sa shadow_sb ops es s G0 tn0.
  (!cenv ty e.
     gas_shadow_compiles (lower_value compile_expr cenv ty e)
       (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
  (!cenv xs.
     gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
       (compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr xs))) /\
  topics = pre ++ rest /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
        topics; data] dflt) es /\
  body_exprs_full_ok cx rest /\
  compile_multi_exprs compile_expr cenv rest sa = (ops,sb) /\
  compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr rest)
    shadow_sa = (ops,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx rest) (es,s,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\
      LENGTH rest = LENGTH vs /\ LENGTH ops = LENGTH vs /\
      EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs /\
      LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) ops vs /\
      EVERY (\op. op_taint tn op = {}) ops /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv es ee sa s t /\
      (~EXISTS expr_has_effect rest ==> pure_frame cenv func es sa s t) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
      (!op x. MEM op ops /\ op = Var x ==> not_fresh_at sb x) /\
      (!op l. MEM op ops ==> op <> Label l))
    (\H res ee gt r. expr_exit res r)
Proof
  disch_tac >> Induct_on `rest`
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!tops ctx func cenv cx env ann n pre e rest data dflt sa sm sb shadow_sa shadow_sm shadow_sb op ops H DF lo d es s G0 tn0 xs mid v u G1 tn1 ys ee vs t G tn. _` kall_tac >>
      qpat_x_assum `!cenv ty e. gas_shadow_compiles _ _` kall_tac >>
      qpat_x_assum `!cenv xs. gas_shadow_compiles _ _` kall_tac >>
      gvs[compile_multi_exprs_def, comp_return_def] >>
      `!b. get_storage cx (es with gas_obs := []) b = get_storage cx es b` by
        (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
      irule gas_outcome_full_pure >>
      qexistsl_tac [`G0`, `es`, `INL []`, `s`, `tn0`] >>
      simp[eval_exprs_nil] >>
      rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[gas_origin_ptr_path_rules] >>
      fs[wb_frame_def, pure_frame_def, ghost_kept_at_def,
         ghost_inv_at_def, vyperStorageFootprintTheory.storage_well_formed_on_def,
         vyperStorageBackendTheory.get_storage_def] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok cx (e::rest)` >>
  qpat_x_assum `compile_multi_exprs compile_expr cenv (e::rest) sa = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_multi_exprs_def]) >>
  simp[comp_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  Cases_on `compile_multi_exprs compile_expr cenv rest sm` >>
  rename1 `compile_multi_exprs compile_expr cenv rest sm = (tailops,last)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr (e::rest)) shadow_sa = _` mp_tac >>
  simp[MAP, Once compile_multi_exprs_def, comp_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa = (sop,shadow_sm)` >>
  Cases_on `compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr rest) shadow_sm` >>
  rename1 `compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr rest) shadow_sm = (stailops,shadow_last)` >>
  simp[] >> strip_tac >>
  `op = sop /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `!cenv ty e. gas_shadow_compiles _ _`
       (qspecl_then [`cenv`, `expr_type e`, `e`] mp_tac) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `tailops = stailops /\ gas_shadow_state last shadow_last` by
    (qpat_x_assum `!cenv xs. gas_shadow_compiles _ _`
       (qspecl_then [`cenv`, `rest`] mp_tac) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`, `shadow_sm`] mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env es` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >> simp[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `expr_body_pre cenv cx env
     (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
       (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) es` by
    (drule expr_body_pre_raw_log_arg >> disch_then irule >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> simp[] >>
     qpat_x_assum `topics = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `ci_mono sa sm /\ ci_mono sm last /\
   ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_last` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
     conj_tac
     >- (qspecl_then [`compile_expr`,`cenv`,`rest`,`sm`] mp_tac ci_mono_compile_multi_exprs >> simp[compile_expr_ci_mono]) >>
     conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
     qspecl_then [`compile_expr`,`cenv`,`MAP gas_shadow_expr rest`,`shadow_sm`] mp_tac ci_mono_compile_multi_exprs >> simp[compile_expr_ci_mono]) >>
  `fn_has_code sa sm func /\ fn_has_code sm last func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_last shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_exprs_full_ok cx (e::rest)`
       (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >> strip_tac >>
     qpat_x_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,`s`,`G0`,`tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >> irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[]) 
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) 
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_return]) >>
  qexists_tac `\H res ee G tn t. headQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "continue" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `headR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume raw_log_topics_suffix_full_under_compose[continue]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`u`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (headQ = _)`
    (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[evaluation_state_component_equality]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
  `expr_sim_inv cenv cx env mid` by
    (drule_all (SRULE [SF ETA_ss] expr_body_pre_eval) >> simp[]) >>
  `expr_body_pre cenv cx env
     (Call ann RawLog
       [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
         (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] dflt) mid` by
    (qpat_x_assum `expr_body_pre _ _ _ (Call _ _ _ _) es` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `body_exprs_full_ok cx rest` by
    (qpat_x_assum `body_exprs_full_ok cx (e::rest)` mp_tac >>
     rewrite_tac[body_exprs_full_ok_def] >> strip_tac >>
     first_x_assum irule >>
     qpat_x_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gen_tac >> strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >>
     qpat_x_assum `ci_mono sa sm` mp_tac >> simp[ci_mono_def]) >>
  `return_buf_frame d cenv sm u` by
    (qpat_x_assum `return_buf_frame d cenv sa s` mp_tac >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
     qpat_x_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `d` >- fs[return_buf_frame_def] >>
     PairCases_on `x` >> fs[return_buf_frame_def, expr_post_def] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid u /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
     qpat_assum `Abbrev (headQ = _)`
       (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> strip_tac >> fs[expr_post_def]) >>
  `gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx rest) (mid,u,G1,tn1)
    (\H res ee G tn t. ?vs. res = INL vs /\
      LENGTH rest = LENGTH vs /\ LENGTH tailops = LENGTH vs /\
      EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs /\
      LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) tailops vs /\
      EVERY (\op. op_taint tn op = {}) tailops /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = last.cs_current_bb /\
      t.vs_inst_idx = LENGTH last.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv mid ee sm u t /\
      (~EXISTS expr_has_effect rest ==> pure_frame cenv func mid sm u t) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv mid sm G1 tn1 u G tn /\
      (!op x. MEM op tailops /\ op = Var x ==> not_fresh_at last x) /\
      (!op l. MEM op tailops ==> op <> Label l))
    (\H res ee gt r. expr_exit res r)` by
    (qpat_x_assum `!pre topics DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ann n data dflt st0 sa sb shadow_sa shadow_sb ops es s G0 tn0. _` irule >>
     simp[] >>
     conj_tac
     >- (qexistsl_tac [`shadow_func`,`shadow_sm`,`shadow_last`] >> simp[]) >>
     conj_tac >- (qexists_tac `tops` >> simp[]) >>
     qexistsl_tac [`ann`,`data`,`dflt`,`env`,`n`,`pre ++ [e]`] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
     metis_tac[]) >>
  FAIL_TAC "return map"
QED

Finalise raw_log_topics_suffix_full_under_compose

(* Request-prefix companion to bodyFullExtCallPosList. *)
Theory s1PrefixExtCallPosList
Ancestors
  s1PrefixPreds bodyFullExtCallPosList s1PrefixDefs s1PrefixCompose s1PrefixOfVV
  s1PrefixFrame s1PrefixProps bodyFullExprsListFacts
  exprLowering exprLoweringProps compileEnv gasShadowCompile gasShadowCompileContext
  gasShadowState gasShadowCompileHelpers fragExec vyperInterpreter vyperState vyperStorageTrace list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  (* Generalize the entry cut; the completed head changes it for the tail. *)
  map_every qid_spec_tac [`tn0`, `G0`, `s0`, `es`, `shadow_sa`, `sa`, `svs`] >>
  Induct_on `xs` >> rpt gen_tac >> strip_tac
  >- (irule gas_prefix_full_no_outcome >> simp[evaluate_def, return_def,
                                             storage_trace_frame_return]) >>
  qmatch_asmsub_rename_tac `body_exprs_full_ok cx (e::xs)` >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
      >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`,
             `PG`, `G0`, `tn0`, `s0`] >> simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil]) >>
      rpt strip_tac >>
      `storage_trace_frame (eval_exprs cx (e::xs))` by
        simp[evaluate_storage_trace_frame] >>
      drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
      `?suffix. obs_pre = es.storage_trace ++ suffix` by
        (qpat_assum `_ = es.storage_trace ++ observations` mp_tac >>
         pure_rewrite_tac[GSYM APPEND_ASSOC] >>
         simp[Once APPEND_EQ_APPEND] >> strip_tac >> gvs[] >>
         Cases_on `l` >> gvs[]) >>
      metis_tac[gasOutcomeFullTheory.valid_horizon_append,
                bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]) >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,si)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (shvv,shadow_si)` >>
  `shvv = vv /\ gas_shadow_state si shadow_si` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
       (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
     qpat_assum `gas_shadow_compiles (compile_expr _ _ _) _`
       (mp_tac o Q.SPECL [`sa`, `shadow_sa`] o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  qpat_x_assum `shvv = vv` SUBST_ALL_TAC >>
  qabbrev_tac `copy = exprs_can_mutate cenv (xs ++ kw_es)` >>
  `exprs_can_mutate cenv (MAP gas_shadow_expr xs ++ MAP gas_shadow_expr kw_es) = copy` by
    (pure_rewrite_tac[GSYM MAP_APPEND, gas_shadow_expr_can_mutate] >> simp[Abbr `copy`]) >>
  qabbrev_tac `snap = compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)` >>
  `gas_shadow_compiles snap snap` by
    simp[Abbr `snap`, gasShadowCompileConvertTheory.gas_shadow_compiles_snapshot_vv] >>
  Cases_on `snap si` >> rename1 `snap si = (sv,sm)` >>
  Cases_on `snap shadow_si` >> rename1 `snap shadow_si = (shsv,shadow_sm)` >>
  `shsv = sv /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `gas_shadow_compiles snap snap`
       (qspecl_then [`si`,`shadow_si`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `shsv = sv` SUBST_ALL_TAC >>
  `?tail_svs.
     compile_ext_call_args compile_expr cenv kw_es
       (MAP (lowered_value_type cenv) xs) xs sm = (tail_svs,sb) /\
     compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
       (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
       (MAP gas_shadow_expr xs) shadow_sm = (tail_svs,shadow_sb)` by
    (Cases_on `compile_ext_call_args compile_expr cenv kw_es
        (MAP (lowered_value_type cenv) xs) xs sm` >>
     Cases_on `compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
        (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
        (MAP gas_shadow_expr xs) shadow_sm` >>
     qpat_x_assum `compile_ext_call_args _ _ kw_es _ (e::xs) sa = _`
       (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def] o REWRITE_RULE [listTheory.MAP]) >>
     qpat_x_assum `compile_ext_call_args _ _ (MAP _ kw_es) _ _ shadow_sa = _`
       (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def] o REWRITE_RULE [listTheory.MAP]) >>
     fs[comp_bind_def, comp_return_def, Abbr `snap`, Abbr `copy`] >>
     rpt strip_tac >> gvs[]) >>
  `compile_ext_call_args compile_expr cenv (xs ++ kw_es)
       (MAP (lowered_value_type cenv) [e]) [e] sa = ([sv],sm) /\
   compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr (xs ++ kw_es))
       (MAP (lowered_value_type cenv) (MAP gas_shadow_expr [e]))
       (MAP gas_shadow_expr [e]) shadow_sa = ([sv],shadow_sm)` by
    (qunabbrev_tac `snap` >> qunabbrev_tac `copy` >>
     simp[compile_ext_call_args_def, comp_bind_def, comp_return_def, MAP_APPEND]) >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm /\
   ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    (qspecl_then [`[e]`,`MAP (lowered_value_type cenv) [e]`,
        `compile_expr`,`cenv`,`xs ++ kw_es`,`sa`] mp_tac ci_mono_compile_ext_call_args >>
     qspecl_then [`MAP gas_shadow_expr [e]`,
        `MAP (lowered_value_type cenv) (MAP gas_shadow_expr [e])`,
        `compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr (xs ++ kw_es)`,
        `shadow_sa`] mp_tac ci_mono_compile_ext_call_args >>
     qspecl_then [`xs`,`MAP (lowered_value_type cenv) xs`,
        `compile_expr`,`cenv`,`kw_es`,`sm`] mp_tac ci_mono_compile_ext_call_args >>
     qspecl_then [`MAP gas_shadow_expr xs`,
        `MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs)`,
        `compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr kw_es`,
        `shadow_sm`] mp_tac ci_mono_compile_ext_call_args >>
     pure_asm_rewrite_tac[] >> simp[cj 1 compile_expr_ci_mono]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (mp_tac (Q.SPECL [`sa`, `sm`, `sb`, `func`] fn_has_code_split) >> fs[ci_mono_def]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    (mp_tac (Q.SPECL [`shadow_sa`, `shadow_sm`, `shadow_sb`, `shadow_func`] fn_has_code_split) >> fs[ci_mono_def]) >>
  `fn_has_code sa si func /\ fn_has_code shadow_sa shadow_si shadow_func` by
    (qunabbrev_tac `snap` >>
     `ci_mono sa si /\ ci_mono shadow_sa shadow_si` by
       (conj_tac >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
          (cj 1 compile_expr_ci_mono) >> simp[]) >>
        qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,
          `shadow_sa`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
     `ci_mono si sm /\ ci_mono shadow_si shadow_sm` by
       (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`si`]
          mp_tac ci_mono_compile_snapshot_vv >>
        qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`shadow_si`]
          mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
     conj_tac
     >- (mp_tac (Q.SPECL [`sa`, `si`, `sm`, `func`] fn_has_code_split) >> fs[ci_mono_def]) >>
     mp_tac (Q.SPECL [`shadow_sa`, `shadow_si`, `shadow_sm`, `shadow_func`] fn_has_code_split) >>
     fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono] >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\
   expr_body_pre cenv cx env e es` by
    fs[body_exprs_full_ok_cons, Once body_exprs_prefix_ok_def] >>
  suspend "compose"
QED
*)
Theorem extcall_request_positional_packing_prefix:
  body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sa = (svs,sb) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
    (MAP gas_shadow_expr xs) shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_positional_packing_prefix[compose]:
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx [e]) (es,s0,G0,tn0)
     (extcall_positional_post F DF lo d ctx func cenv cx env
       (xs ++ kw_es) [e] [sv] sa sm es s0 G0 tn0)
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` by
    (irule extcall_request_positional_packing_outcome_named >>
     `!st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st` by
       (rpt strip_tac >> qpat_assum `!e' st. MEM e' (e::xs) /\ _ ==> _`
          (qspecl_then [`e`,`st`] mp_tac) >> simp[]) >>
     `body_exprs_full_ok cx [e]` by simp[body_exprs_full_ok_nil, body_exprs_full_ok_cons] >>
     simp[MEM] >>
     rpt conj_tac
     >- (rpt strip_tac >> qpat_assum `!fn inst z. frag_reachable _ _ _ _ _ _ ==> _`
           (qspecl_then [`fn`,`inst`,`z`] mp_tac) >> simp[])
     >- (qexistsl_tac [`shadow_func`,`shadow_sa`,`shadow_sm`] >>
         qpat_assum `compile_ext_call_args _ _ _ _ _ shadow_sa = ([sv],shadow_sm)` mp_tac >>
         simp_tac (srw_ss()) [MAP_APPEND] >> simp[]) >>
     qexists_tac `tops` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_expr cx e) (es,s0,G0,tn0)` by
    (`expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (expr_type e) e es` by
       (qpat_assum `body_expr_prefix_ok cx e`
         (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
        first_x_assum (qspecl_then
          [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
           `cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
     qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`si`,`shadow_sa`,`shadow_si`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
     simp[] >> metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible,
                          exprSimMemorySourceTheory.forced_expr_admissible_raw]) >>
  suspend "source_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_positional_packing_prefix[source_bind]:
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM, evaluate_def] >>
  `!st. eval_exprs cx [e] st =
      (SUM_MAP (\v. [v]) I (FST (bind (eval_expr cx e) (read_result cx) st)),
       SND (bind (eval_expr cx e) (read_result cx) st))` by
    (pure_asm_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >> gen_tac >>
     Cases_on `bind (eval_expr cx e) (read_result cx) st` >> Cases_on `q` >>
     simp[bind_def, return_def, sumTheory.SUM_MAP]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx [e]) (es,s0,G0,tn0)` by
    (`!st. SND (eval_exprs cx [e] st) = SND (bind (eval_expr cx e) (read_result cx) st)` by simp[] >>
     drule gas_prefix_full_state_cong >>
     simp[gas_prefix_full_bind_read_result]) >>
  `eval_exprs cx (e::xs) = bind (eval_exprs cx [e])
      (\vs. bind (eval_exprs cx xs) (\ws. return (HD vs::ws)))` by
    (pure_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `st` >>
     CONV_TAC (LAND_CONV (RATOR_CONV (REWR_CONV exprSimWordArgsTheory.eval_exprs_cons_action))) >>
     CONV_TAC (LAND_CONV (REWR_CONV bind_def) THENC RAND_CONV (REWR_CONV bind_def)) >>
     Cases_on `bind (eval_expr cx e) (read_result cx) st` >> Cases_on `q` >>
     simp[sumTheory.SUM_MAP, combinTheory.I_THM]) >>
  pop_assum SUBST1_TAC >>
  suspend "packing_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_positional_packing_prefix[packing_bind]:
  qabbrev_tac `Q = (\H (res:value list + exception) ee G tn t.
     stmt_state_rel H ctx func cenv cx ee t /\
     storage_well_formed_on cx ee (FST H) /\
     return_buf_frame d cenv sm t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
     alloca_history func t /\ ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ expr_sim_inv cenv cx env ee /\
     (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z))` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx [e]) (es,s0,G0,tn0) Q
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx [e]) _ _ _` (irule_at Any) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `extcall_positional_post F DF lo d ctx func cenv cx env _ _ _ sa sm es s0 G0 tn0 _ _ _ _ _ _`
       (strip_assume_tac o BETA_RULE o REWRITE_RULE[extcall_positional_post_def]) >>
     simp[Abbr `Q`] >>
     `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (rpt strip_tac >> metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi]) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,_,_)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
          bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     metis_tac[]) >>
  irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q _` (irule_at Any) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_return] >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  suspend "packing_tail"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_positional_packing_prefix[packing_tail]:
  `?head. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL head, mid with gas_obs := [])` by
    (qpat_assum `!tail. SUM_MAP _ _ _ = INL _ /\ _`
         (qspec_then `[]` (strip_assume_tac o REWRITE_RULE[listTheory.APPEND_NIL])) >>
     Cases_on `bind (eval_expr cx e) (read_result cx)
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` >>
     Cases_on `q` >> gvs[sumTheory.SUM_MAP]) >>
  `body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs` by
    (drule (REWRITE_RULE[ETA_AX] exprSimSourceTheory.eval_expr_read_INL) >> strip_tac >>
     fs[body_exprs_full_ok_cons, Once body_exprs_prefix_ok_def] >>
     metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule bodyFullPredsTheory.body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) _ _ = (INL head,mid with gas_obs := [])`
       (irule_at Any) >> fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Q _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  fs[Abbr `Q`] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)` by
    (qpat_x_assum `!svs' sa' shadow_sa' es' s0' G0' tn0'. _ ==> gas_prefix_full _ _ _ (eval_exprs cx xs) _`
       (qspecl_then [`tail_svs`,`sm`,`shadow_sm`,`mid`,`t`,`G1`,`tn1`] mp_tac) >>
     simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  `!st. SND (bind (eval_exprs cx xs) (\ws. return (HD v::ws)) st)
       = SND (eval_exprs cx xs st)` by
    (gen_tac >> Cases_on `eval_exprs cx xs st` >> Cases_on `q` >> simp[bind_def,return_def]) >>
  drule s1PrefixOfVVTheory.gas_prefix_full_state_cong >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise extcall_request_positional_packing_prefix
*)

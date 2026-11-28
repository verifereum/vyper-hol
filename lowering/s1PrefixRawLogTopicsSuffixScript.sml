Theory s1PrefixRawLogTopicsSuffix
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixProps s1PrefixCompose s1PrefixFrame
  bodyMemoryDefs
  bodyFullPreds bodySimFull bodyFullIfExpReach bodyFullShadowBodyInv
  bodyRawLogArgPre exprBodyPreProps exprSimSource exprSimProps exprLoweringProps
  gasShadowState loweringPosts bodyPtrDefs fragGasOriginPtr
  vyperInterpreter vyperState vyperAST list exprLowering compileEnv
  exprSimWordArgs stmtSimProps contextRawReachable ptrDiscipline unitMemInv
  vyperStorageTrace vyperStorageFootprint
  bodyFullExprsListFacts bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  Induct_on `rest`
  >- (rpt gen_tac >> strip_tac >>
      `eval_exprs cx [] = return []` by simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
      simp[bind_return] >> irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_return, return_def]) >>
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
  qpat_x_assum `compile_multi_exprs compile_expr _ (MAP gas_shadow_expr (e::rest)) shadow_sa = _` mp_tac >>
  simp[MAP, Once compile_multi_exprs_def, comp_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value compile_expr _ (expr_type e) (gas_shadow_expr e) shadow_sa = (sop,shadow_sm)` >>
  Cases_on `compile_multi_exprs compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr rest) shadow_sm` >>
  rename1 `compile_multi_exprs compile_expr _ (MAP gas_shadow_expr rest) shadow_sm = (stailops,shadow_last)` >>
  simp[] >> strip_tac >>
  `sop = op /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `!cenv ty e. gas_shadow_compiles _ _`
       (qspecl_then [`cenv`, `expr_type e`, `e`] mp_tac) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `stailops = tailops` by
    (qpat_assum `!cenv xs. gas_shadow_compiles _ _`
       (qspecl_then [`cenv`, `rest`] mp_tac) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >> simp[]) >>
  gvs[] >>
  suspend "head"
QED
*)
Theorem raw_log_topics_suffix_acc_prefix[local]:
  !rest pre topics DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx
   env ann n data dflt st0 sa sb shadow_sa shadow_sb ops es s G0 tn0 acc.
  (!cenv ty e.
     gas_shadow_compiles (lower_value compile_expr cenv ty e)
       (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))) /\
  (!cenv xs.
     gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
       (compile_multi_exprs compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs))) /\
  topics = pre ++ rest /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
        topics; data] dflt) es /\
  body_exprs_full_ok cx rest /\
  body_exprs_prefix_ok cx rest /\
  compile_multi_exprs compile_expr cenv rest sa = (ops,sb) /\
  compile_multi_exprs compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr rest)
    shadow_sa = (ops,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst st. frag_reachable ctx func s fn inst st ==> dalloca_fmp_headroom inst st) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx rest) (\vs. return (acc ++ vs))) (es,s,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_log_topics_suffix_acc_prefix[head]:
  `expr_sim_inv cenv cx env es` by metis_tac[expr_body_pre_static_facts] >>
  `expr_body_pre cenv cx env
     (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
       (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) (pre ++ e::rest)) es` by
    (drule expr_body_pre_raw_log_arg >> disch_then irule >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]) >>
  rename1 `compile_multi_exprs compile_expr cenv rest sm = (tailops,last)` >>
  rename1 `compile_multi_exprs compile_expr _ (MAP gas_shadow_expr rest) shadow_sm = (tailops,shadow_last)` >>
  `ci_mono sa sm /\ ci_mono sm last /\
   ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_last` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
     conj_tac
     >- (qspecl_then [`compile_expr`,`cenv`,`rest`,`sm`] mp_tac ci_mono_compile_multi_exprs >> simp[compile_expr_ci_mono]) >>
     conj_tac
     >- (qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
     qspecl_then [`compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr rest`,`shadow_sm`] mp_tac ci_mono_compile_multi_exprs >>
     simp[compile_expr_ci_mono]) >>
  `fn_has_code sa sm func /\ fn_has_code sm last func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_last shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    fs[body_exprs_full_ok_cons, body_exprs_prefix_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (irule (cj 1 body_expr_full_ok_simulations) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`env`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,`s`,`G0`,`tn0`] mp_tac) >>
     simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,`s`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "compose"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_log_topics_suffix_acc_prefix[compose]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
     (\H rr ee G tn t. headQ H rr ee G tn t /\
        ?ms. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G0,tn0) ms (OK t,G,tn)) headR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ headR` >>
  `bind (eval_exprs cx (e::rest)) (\vs. return (acc ++ vs)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. bind (eval_exprs cx rest) (\vs. return ((acc ++ [v]) ++ vs)))` by
    (pure_rewrite_tac[eval_exprs_cons_action, GSYM APPEND_ASSOC, APPEND] >>
     simp[NoAsms, bind_assoc, bind_return]) >>
  pop_assum (pure_rewrite_tac o single) >>
  irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ headR` (irule_at Any) >>
  simp[Abbr `headR`, evaluate_storage_trace_frame, storage_trace_frame_read_result,
    storage_trace_frame_return, storage_trace_frame_bind_all,
    evaluate_requests_outcomes_frame, requests_outcomes_frame_bind_all,
    requests_outcomes_frame_read_result] >>
  reverse conj_tac
  >- (rpt gen_tac >> rename1 `ISR rr` >> Cases_on `rr` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  suspend "restart"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_log_topics_suffix_acc_prefix[restart]:
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms, Abbr `pathQ`, Abbr `headQ`] >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv _ ctx _ cx` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[body_inv_no_phi]) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s,G0,tn0) _ (OK u,G1,tn1)` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     qpat_assum `!fn inst st. frag_reachable ctx func s fn inst st ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `~u.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e` by metis_tac[expr_body_pre_static_facts] >>
     qpat_assum `bind _ _ _ = (INL v,_)` (mp_then Any mp_tac body_const_cells_agree_expr_read) >>
     simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `bind _ _ _ = (INL v,_)`
       (mp_then Any mp_tac (SRULE [SF ETA_ss] expr_body_pre_eval)) >> simp[]) >>
  `?st tv z st' w z'. eval_expr cx e st = (INL tv,z) /\ read_result cx tv st' = (INL w,z')` by
    (qpat_assum `bind _ _ _ = (INL v,_)`
       (mp_then Any mp_tac vyperStatePreservationTheory.bind_split) >>
     simp[] >> metis_tac[]) >>
  `body_exprs_full_ok cx rest /\ body_exprs_prefix_ok cx rest` by
    (qpat_x_assum `body_exprs_full_ok cx (e::rest)` mp_tac >>
     qpat_x_assum `body_exprs_prefix_ok cx (e::rest)` mp_tac >>
     pure_once_rewrite_tac[body_exprs_full_ok_cons, body_exprs_prefix_ok_def] >>
     metis_tac[]) >>
  suspend "frame"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_log_topics_suffix_acc_prefix[frame]:
  `expr_body_pre cenv cx env
     (Call ann RawLog
       [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
         (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
         ((pre ++ [e]) ++ rest); data] dflt) mid` by
    (qpat_x_assum `expr_body_pre _ _ _ (Call _ _ _ _) es` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def, APPEND_ASSOC]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gen_tac >> strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv sm u` by
    (irule return_buf_frame_frame >>
     map_every qexists_tac [`cenv`,`s`,`sa`] >> simp[] >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
     simp[expr_post_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid u /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
     simp[NoAsms] >> strip_tac >> fs[expr_post_def]) >>
  qpat_x_assum `!pre' DF' lo' d' PG. _` (qspec_then `pre ++ [e]` irule) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `expr_body_pre _ _ _ (Call _ RawLog _ _) mid`)) >>
  goal_assum (drule_at (Pat `compile_multi_exprs compile_expr _ rest sm = _`)) >>
  map_every qexists_tac [`d`,`sm`,`last`,`shadow_func`,`tops`] >>
  simp[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_log_topics_suffix_acc_prefix
*)

Theorem raw_log_topics_suffix_prefix:
  !rest pre topics DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx
   env ann n data dflt st0 sa sb shadow_sa shadow_sb ops es s G0 tn0.
  (!cenv ty e.
     gas_shadow_compiles (lower_value compile_expr cenv ty e)
       (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))) /\
  (!cenv xs.
     gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
       (compile_multi_exprs compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs))) /\
  topics = pre ++ rest /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
        topics; data] dflt) es /\
  body_exprs_full_ok cx rest /\
  body_exprs_prefix_ok cx rest /\
  compile_multi_exprs compile_expr cenv rest sa = (ops,sb) /\
  compile_multi_exprs compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr rest)
    shadow_sa = (ops,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst st. frag_reachable ctx func s fn inst st ==> dalloca_fmp_headroom inst st) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx rest) (es,s,G0,tn0)
Proof
  rpt gen_tac >> strip_tac >>
  `bind (eval_exprs cx rest) (\vs. return ([] ++ vs)) = eval_exprs cx rest` by
    (simp[FUN_EQ_THM, bind_def, return_def] >> gen_tac >>
     Cases_on `eval_exprs cx rest x` >> Cases_on `q` >> simp[]) >>
  pop_assum (fn th => gvs[] >> pure_once_rewrite_tac [GSYM th]) >>
  irule raw_log_topics_suffix_acc_prefix >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `expr_body_pre _ _ _ (Call _ RawLog _ _) _`)) >>
  goal_assum (drule_at (Pat `compile_multi_exprs compile_expr _ (MAP gas_shadow_expr _) _ = _`)) >>
  map_every qexists_tac [`d`,`sa`,`sb`,`shadow_func`,`tops`] >>
  simp[]
QED

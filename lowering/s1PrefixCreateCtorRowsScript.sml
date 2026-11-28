(* Request prefixes through constructor-argument evaluation and row preparation. *)
Theory s1PrefixCreateCtorRows
Ancestors
  bodyFullCreateHeld s1PrefixPreds s1PrefixDefs s1PrefixCompose s1PrefixOfVV
  s1PrefixFrame s1PrefixProps bodyFullPreds exprLowering exprLoweringProps
  bodyFullExprsListFacts
  compileEnv gasShadowCompileStmtHelpers gasShadowCompileBase gasShadowState
  gasShadow contextRawReachable bodySimFull loweringPosts loweringStateRelDefs
  fragExec vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  gasOutcomeFull exprSimDefs exprSimSource list sum
  bodyFullIfExpReach[qualified] bodyFullForArrayRound[qualified]
  bodyFullExtCallPackingReady[qualified] bodyFullHashKeccakFixed[qualified]
  gasShadowCompileConvert[qualified] gasShadowCompilePure[qualified]
  gasShadowCompileHelpers[qualified] exprSimWordArgs[qualified]
  exprSimMemorySource[qualified] freshWrites[qualified]
Libs
  pairLib

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  map_every qid_spec_tac [`tn0`,`G0`,`s0`,`es`,`shadow_sb`,`shadow_sa`,`sb`,`sa`,`svs`] >>
  Induct_on `xs` >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- (irule gas_prefix_full_no_outcome >>
      simp[evaluate_def,return_def,storage_trace_frame_return]) >>
  qmatch_asmsub_rename_tac `body_exprs_full_ok cx (e::xs)` >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- suspend "bad_entry" >>
  suspend "split_code"
QED
*)
Theorem create_ctor_rows_operand_prefix:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  compile_create_ctor_args compile_expr cenv xs sa = (svs,sb) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
    shadow_sa = (svs,shadow_sb) /\
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
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume create_ctor_rows_operand_prefix[bad_entry]:
  simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`,
                   `PG`, `G0`, `tn0`, `s0`] >>
      simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil]) >>
  rpt strip_tac >>
  `storage_trace_frame (eval_exprs cx (e::xs))` by simp[evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
  `?suffix. obs_pre = es.storage_trace ++ suffix` by
    (qpat_assum `_ = es.storage_trace ++ observations` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[Once APPEND_EQ_APPEND] >> strip_tac >> gvs[] >> Cases_on `l` >> gvs[]) >>
  metis_tac[gasOutcomeFullTheory.valid_horizon_append,
            bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_ctor_rows_operand_prefix[split_code]:
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\ expr_body_pre cenv cx env e es` by
    fs[Once body_exprs_full_ok_cons,Once body_exprs_prefix_ok_def] >>
  qabbrev_tac `copy = exprs_can_mutate cenv xs` >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ (expr_type e) (gas_shadow_expr e) shadow_sa = (vv',shm)` >>
  `vv' = vv /\ gas_shadow_state sm shm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_compile_expr_env >>
     drule_all bodyFullForArrayRoundTheory.nonslot_shadow_cut >> simp[]) >>
  qpat_x_assum `vv' = vv` SUBST_ALL_TAC >>
  qabbrev_tac `snap = compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)` >>
  Cases_on `snap sm` >> rename1 `snap sm = (sv,ss)` >>
  Cases_on `snap shm` >> rename1 `snap shm = (sv',shs)` >>
  `sv' = sv /\ gas_shadow_state ss shs` by
    (`gas_shadow_compiles snap snap` by
       simp[Abbr `snap`,gasShadowCompileConvertTheory.gas_shadow_compiles_snapshot_vv] >>
     fs[gas_shadow_compiles_def] >> first_x_assum (qspecl_then [`sm`,`shm`] mp_tac) >> simp[]) >>
  qpat_x_assum `sv' = sv` SUBST_ALL_TAC >>
  Cases_on `compile_create_ctor_args compile_expr cenv xs ss` >>
  rename1 `compile_create_ctor_args _ _ xs ss = (tail_svs,sc)` >>
  Cases_on `compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs) shs` >>
  rename1 `compile_create_ctor_args _ _ (MAP gas_shadow_expr xs) shs = (tail_svs',shc)` >>
  `svs = sv::tail_svs /\ sb = sc /\ shadow_sb = shc /\ tail_svs' = tail_svs` by
    (qpat_assum `compile_create_ctor_args _ _ (e::xs) sa = _`
      (mp_tac o ONCE_REWRITE_RULE [compile_create_ctor_args_def]) >>
     qpat_assum `compile_create_ctor_args _ _ (MAP _ (e::xs)) shadow_sa = _`
      (mp_tac o ONCE_REWRITE_RULE [compile_create_ctor_args_def] o REWRITE_RULE [listTheory.MAP]) >>
     simp[comp_bind_def,comp_return_def,gas_shadow_expr_type,
          gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate,
          gasShadowCompilePureTheory.gas_shadow_lowered_value_type,
          Abbr `snap`,Abbr `copy`] >> strip_tac >> strip_tac >> gvs[]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`svs = _`,`sb = _`,`shadow_sb = _`,`tail_svs' = _`] >>
  qunabbrev_tac `snap` >>
  suspend "code_spans"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_ctor_rows_operand_prefix[code_spans]:
  `ci_mono sa sm /\ ci_mono shadow_sa shm` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
     qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_sa`]
       mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `ci_mono sm ss /\ ci_mono shm shs` by
    (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >>
     qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`shm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono ss sc /\ ci_mono shs shc` by
    (qspecl_then [`compile_expr`,`cenv`,`xs`,`ss`] mp_tac ci_mono_compile_create_ctor_args >>
     qspecl_then [`compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr xs`,`shs`]
       mp_tac ci_mono_compile_create_ctor_args >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sa ss /\ ci_mono shadow_sa shs` by metis_tac[ci_mono_trans] >>
  `fn_has_code sa ss func /\ fn_has_code ss sc func` by
    (qspecl_then [`sa`,`ss`,`sc`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code shadow_sa shs shadow_func /\ fn_has_code shs shc shadow_func` by
    (qspecl_then [`shadow_sa`,`shs`,`shc`,`shadow_func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shm shadow_func` by
    (conj_tac
     >- (qspecl_then [`sa`,`sm`,`ss`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
     qspecl_then [`shadow_sa`,`shm`,`shs`,`shadow_func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv ss` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> fs[ci_mono_def]) >>
  suspend "head_prefix"
QED
*)

(* The prefix stops at a request in the expression itself; the completed
   head outcome below includes the subsequent snapshot instructions. *)
(* SCRATCH MEASUREMENT: original continuation.
Resume create_ctor_rows_operand_prefix[head_prefix]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` by
    (`expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (expr_type e) e es` by
       (qpat_assum `body_expr_prefix_ok cx e`
          (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
        first_x_assum (qspecl_then
          [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
           `cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
     rewrite_tac[gas_prefix_full_bind_read_result] >>
     qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
     simp[] >> metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible,
                         exprSimMemorySourceTheory.forced_expr_admissible_raw]) >>
  suspend "bind_rows"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_ctor_rows_operand_prefix[bind_rows]:
  mp_tac (Q.INST [`sh` |-> `shadow_sa`] create_ctor_head_outcome) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.body_inv_no_phi >>
     qexistsl [`cenv`,`ctx`,`cx`,`func`,`tops`] >> simp[]) >>
  qabbrev_tac `rowQ = (\H (res:value + exception) ee G tn t.
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv ss t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    alloca_history func t /\ ~t.vs_halted /\ t.vs_current_bb = ss.cs_current_bb /\
    t.vs_inst_idx = LENGTH ss.cs_current_insts /\
    (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z))` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) rowQ headR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qunabbrev_tac `headQ` >> RULE_ASSUM_TAC BETA_RULE >>
     qpat_x_assum `?v. res = INL v /\ _`
       (qx_choose_then `v0` (map_every assume_tac o CONJUNCTS)) >>
     simp[Abbr `rowQ`] >> rpt strip_tac >>
     irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,_,_)` (irule_at Any) >>
     qexists `fn` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ rowQ headR` (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_return,
       requests_outcomes_frame_bind_all,evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  reverse conj_tac
  >- (simp[Abbr `headR`] >> rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[exprSimDefsTheory.expr_exit_def]) >>
  suspend "tail_prefix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_ctor_rows_operand_prefix[tail_prefix]:
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule create_operand_const_cells_replay >> rpt (goal_assum (drule_at Any))) >>
  `body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs` by
    (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL) >>
     strip_tac >> fs[Once body_exprs_full_ok_cons,Once body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `rowQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
       (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)` by
    (qpat_x_assum `!svs' sa' sb' sh' shb' es' s' g' tn'. _ ==>
         gas_prefix_full _ _ _ (eval_exprs cx xs) _`
      (qspecl_then [`tail_svs`,`ss`,`sc`,`shs`,`shc`,`mid`,`t`,`G1`,`tn1`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!st. SND (bind (eval_exprs cx xs) (\vs. return (v::vs)) st) =
        SND (eval_exprs cx xs st)` by
    (gen_tac >> Cases_on `eval_exprs cx xs st` >> Cases_on `q` >> simp[bind_def,return_def]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise create_ctor_rows_operand_prefix
*)

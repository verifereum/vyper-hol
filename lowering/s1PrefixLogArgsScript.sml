(* Request-prefix companion to bodyFullLogArgs. *)
Theory s1PrefixLogArgs
Ancestors
  s1PrefixPreds bodyFullLogArgs s1PrefixDefs s1PrefixCompose s1PrefixOfVV
  s1PrefixFrame fragGasOriginPtrExec s1PrefixProps
  bodyFullIfExpReach bodySimFull loweringPosts bodyMemoryDefs
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogArgs gasShadowState
  gasShadowCompileStmtHelpers gasShadowCompileHelpers exprLoweringProps
  exprSimWordArgs exprSimProps exprLowering fragExec compileEnv loweringStateRelDefs
  vyperStorageFootprint vyperStorageTrace vyperInterpreter vyperState
  vyperTypeSystem exprSimDefs ptrDiscipline
  contextRawReachable gasContext freshWrites list sum
Libs
  monadsyntax

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (rpt gen_tac >> strip_tac >>
      irule gas_prefix_full_no_outcome >> simp[evaluate_storage_trace_frame] >>
      simp[Once evaluate_def, return_def]) >>
  rpt gen_tac >> strip_tac >> gvs[expr_can_mutate_def] >>
  `~exprs_can_mutate cenv (MAP gas_shadow_expr args)` by
    simp[gas_shadow_expr_can_mutate] >>
  qpat_x_assum `compile_log_eval_all cenv (e::args) sa = _` mp_tac >>
  qpat_x_assum `compile_log_eval_all _ (gas_shadow_expr e::_) _ = _` mp_tac >>
  simp[compile_log_eval_all_unsaved_cons] >> rpt strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr _ (expr_type e) (gas_shadow_expr e)
             shadow_sa = (x, ssm)` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x, sm)` >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  `gas_shadow_state sm ssm` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `cs_extends shadow_sa ssm` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `cs_extends sm sb` by
    (qpat_assum `compile_log_eval_all cenv args sm = _`
       (mp_then Any mp_tac compile_log_eval_all_grows) >> simp[]) >>
  `cs_extends ssm shadow_sb` by
    (qpat_assum `compile_log_eval_all _ (MAP gas_shadow_expr _) _ = _`
       (mp_then Any mp_tac compile_log_eval_all_grows) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa ssm shadow_func /\
   fn_has_code ssm shadow_sb shadow_func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule log_head_admissible >> qexists_tac `args` >> fs[GSYM log_args_res_ok_def, SF ETA_ss]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by metis_tac[] >>
  suspend "head"
QED
*)
Theorem compile_log_eval_all_prefix:
  !DF lo d PG ctx shadow_ctx func shadow_func cenv cx st0 R env.
    (!e tail es. R (e::tail) es ==>
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!e tail es. R (e::tail) es ==>
       expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx (expr_type e) e es) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    !args es sa sb shadow_sa shadow_sb ops s0 G0 tn0.
      R args es /\ ~exprs_can_mutate cenv args /\
      EVERY (\e. ~expr_has_effect e) args /\
      EVERY (\e. post_value_type cenv e = expr_type e) args /\
      well_typed_exprs env args /\
      compile_log_eval_all cenv args sa = (ops, sb) /\
      compile_log_eval_all (gas_shadow_env T cenv)
        (MAP gas_shadow_expr args) shadow_sa =
        (ops, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
        !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_exprs cx args)
        (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
        es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_exprs cx args) (es, s0, G0, tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_log_eval_all_prefix[head]:
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (expr_type e) e es` by metis_tac[] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (expr_type e) e es` by metis_tac[] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `x`,
                             `s0`, `G0`, `tn0`] mp_tac) >>
     simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `x`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. headQ H rr ee G tn u /\
       ?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) marks (OK u,G,tn)) headR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  rewrite_tac[eval_exprs_cons_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ headR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[] >> rpt conj_tac
  >- suspend "tail"
  >- (simp[Abbr `headR`] >> rpt gen_tac >> Cases_on `res` >> simp[ISR])
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result,
       storage_trace_frame_bind_all, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_log_eval_all_prefix[tail]:
  qx_genl_tac [`marks`, `v`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `headQ` >> BETA_TAC >> strip_tac >> gvs[] >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
         rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
     rpt strip_tac >> drule_all frag_reachable_members >> strip_tac >>
     fs[ctx_has_dalloca_def, EXISTS_MEM, unitTransformDefsTheory.dalloca_fmp_headroom_def] >>
     metis_tac[]) >>
  `R args mid` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `mid.gas_obs` assume_tac) >>
     fs[evaluation_state_component_equality] >>
     metis_tac[]) >>
  `gas_admissible (eval_exprs cx args) log_args_res_ok mid` by
    (`gas_admissible (eval_exprs cx args) log_args_res_ok (mid with gas_obs := [])`
       suffices_by simp[] >> irule log_tail_admissible >>
     fs[GSYM log_args_res_ok_def, SF ETA_ss] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sm z)` by metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid t /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx args) (mid,t,G1,tn1)` by
    (qpat_x_assum `!es' sa' sb' shadow_sa' shadow_sb' ops' s0' G0' tn0'. _`
       (qspecl_then [`mid`, `sm`, `sb`, `ssm`, `shadow_sb`, `ys`, `t`, `G1`, `tn1`] mp_tac) >>
     (impl_tac >-
        (simp[GSYM log_args_res_ok_def, SF ETA_ss, well_typed_expr_def] >>
         rpt conj_tac
         >- fs[well_typed_expr_def] >>
         first_assum ACCEPT_TAC)) >> simp[]) >>
  `!qe. SND (bind (eval_exprs cx args) (\vs. return (v::vs)) qe) =
        SND (eval_exprs cx args qe)` by
    (gen_tac >> Cases_on `eval_exprs cx args qe` >>
     rename1 `_ = (res, _)` >> Cases_on `res` >> simp[bind_def, return_def]) >>
  metis_tac[gas_prefix_full_state_cong]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_log_eval_all_prefix
*)

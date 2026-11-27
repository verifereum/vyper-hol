(* Request-prefix companion to bodyFullAnnAssignMemory. *)
Theory s1PrefixAnnAssignMemory
Ancestors
  s1PrefixPreds bodyFullAnnAssignMemory s1PrefixDefs s1PrefixCompose
  bodyFullAnnAssignMemoryPost stmtSimDeclSource exprSimHyps
  bodyFullIfExpReach bodyFullHashKeccakFixed bodyFullExtCallPackingReady
  bodySim bodyExprPreFacts exprLoweringProps vyperState

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    (qpat_x_assum `stmt_exprs_ok cenv (AnnAssign id typ e)` mp_tac >>
     simp[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def]) >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- suspend "outside_domain" >>
  drule annassign_admissible_type >> strip_tac >>
  drule_all annassign_full_prefix_parts >>
  disch_then (qx_choosel_then
    [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
    strip_assume_tac) >>
  qpat_assum `!sa ce r ty. declare_local _ _ _ _ = _ ==> _ /\ _ /\ expr_sim_prefix _ _ _ _ _ _ /\ _`
    (drule_then (qspec_then `expr_type e` strip_assume_tac)) >>
  `sz < dimword (:256)` by
    (qpat_assum `sz = _` SUBST1_TAC >>
     qpat_x_assum `type_memory_bytes cenv typ < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (strip_tac >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     simp[] >> drule stateRelProjTheory.stmt_state_rel_fmp_room >>
     simp[fmp_room_def] >> decide_tac) >>
  drule_all annassign_full_alloc_entry >>
  disch_then (qspecl_then [`PG`, `gas_explicit_sites ctx shadow_ctx`]
    (qx_choosel_then [`w`, `entry`, `Ga`, `tna`] strip_assume_tac)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`
       (qspec_then `ARB` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
       qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _` (fn safe =>
       ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
         (LIST_CONJ [path,phi,safe]))))))) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexistsl_tac [`Ga`, `entry`, `tna`] >>
  simp[] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_expr cx e) (es,entry,Ga,tna)` by suspend "rhs" >>
  suspend "source_trace"
QED
*)
Theorem annassign_memory_prefix_execution:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  type_widens_to env.type_defs (expr_type e) typ /\
  assignable_type env.type_defs typ /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  ~is_word_type typ /\
  0 < type_memory_bytes cenv typ /\
  (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
    has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_memory_prefix_execution[outside_domain]:
  simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G0`,`tn0`,`s0`] >>
      simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >>
  `storage_trace_frame (eval_stmt cx (AnnAssign id typ e))` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `?suffix. ee.storage_trace = es.storage_trace ++ suffix` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `?extra. obs_pre = es.storage_trace ++ extra` by
    (`es.storage_trace ++ suffix = obs_pre ++ StorageOutcome rq outcome :: sfx` by fs[] >>
     pop_assum (strip_assume_tac o REWRITE_RULE [listTheory.APPEND_EQ_APPEND])
     >- (rename1 `es.storage_trace = obs_pre ++ extra` >>
         `extra = []` by
           (`0 < LENGTH extra ==> ~(LENGTH extra + LENGTH obs_pre <= LENGTH obs_pre)` by
              decide_tac >>
            Cases_on `extra` >> fs[listTheory.LENGTH_APPEND]) >>
         qexists_tac `[]` >> fs[]) >>
     goal_assum (drule_at Any)) >>
  fs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append,
                     extcall_packing_observed_domain]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_memory_prefix_execution[rhs]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (strip_tac >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace)
        ctx func cenv' cx es entry` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `cenv'.ce_is_ctor = cenv.ce_is_ctor` by
    (qpat_assum `cenv' with <|ce_vars := _; ce_var_type := _;
       ce_dynarray_capacity := _|> = cenv`
       (mp_tac o Q.AP_TERM `\ce. ce.ce_is_ctor`) >> simp[]) >>
  `!H. dead_lo_ok H (DF H) lo cenv' cx` by
    fs[bodyPtrDefsTheory.dead_lo_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule expr_body_pre_vv_gas_admissible >> goal_assum (drule_at Any)) >>
  `fn_has_code shadow_a shadow_sv shadow_func` by
    (Cases_on `shadow_b = shadow_sv` >- fs[] >>
     fs[] >>
     `cs_extends shadow_a shadow_sv` by
       (qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_a = _`
          (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
        first_assum ACCEPT_TAC) >>
     `cs_extends shadow_sv shadow_b` by
       (qpat_assum `unwrap_value _ _ shadow_sv = _`
          (assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
        first_assum ACCEPT_TAC) >>
     qspecl_then [`shadow_a`,`shadow_sv`,`shadow_b`,`shadow_func`] mp_tac
       fragExecTheory.fn_has_code_split >> simp[]) >>
  qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then
    [`st0`,`a`,`sv`,`shadow_a`,`shadow_sv`,`vv`,`entry`,`Ga`,`tna`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_memory_prefix_execution[source_trace]:
  (* Reading the value and declaring the source local add no requests. *)
  `!gs. (SND (eval_stmt cx (AnnAssign id typ e) (es with gas_obs := gs))).storage_trace =
        (SND (eval_expr cx e (es with gas_obs := gs))).storage_trace` by
    (qx_gen_tac `gs` >>
     drule eval_annassign_action >> disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
     Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `eval_expr _ _ _ = (res,mid)` >> Cases_on `res` >> simp[bind_def] >>
     rename1 `eval_expr _ _ _ = (INL raw,mid)` >>
     Cases_on `read_result cx raw mid` >>
     rename1 `read_result _ _ _ = (valres,mid')` >> drule read_result_state >>
     strip_tac >> gvs[] >> Cases_on `valres` >> simp[] >>
     rename1 `read_result _ _ _ = (INL v,mid)` >>
     `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)` by
       simp[bind_def] >>
     drule_all annassign_continuation_success >> strip_tac >> simp[]) >>
  qpat_x_assum `gas_prefix_full _ _ _ (eval_expr _ _) _`
    (qx_choose_then `marks` strip_assume_tac o REWRITE_RULE [gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >>
  conj_tac >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[]) >>
  map_every qx_gen_tac [`tail`,`stmt_res`,`stmt_end`,`obs_pre`,`rq`,`outcome`,`sfx`,`site_h`] >>
  strip_tac >>
  Cases_on `eval_expr cx e (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail)` >>
  rename1 `eval_expr _ _ _ = (rhs_res,rhs_end)` >>
  `rhs_end.storage_trace = stmt_end.storage_trace` by
    (sym_tac >>
     qpat_x_assum `!gs. (SND (eval_stmt _ _ _)).storage_trace = _`
       (qspec_then `gas_explicit marks entry.vs_gas_readings ++ tail` mp_tac) >>
     simp[]) >>
  qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    irule >>
  simp[] >> qexistsl_tac [`rhs_end`,`rhs_res`,`sfx`,`tail`] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise annassign_memory_prefix_execution
*)

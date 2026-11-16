(* Private immutable-array callback boundary: retain the full exceptional post. *)
Theory bodyFullForArrayImmBody
Ancestors
  bodySimFull bodyFullPreds bodyExprPreFacts gasOutcomeFullCompose
  gasOutcomeFullStmts stmtForRangeMemoryRound stmtSimForArrayLoop
  stmtSimDefs stmtSimForRounds fragGasOriginPtr vyperInterpreter vyperState
  vyperStorageTrace gasStorage gasEvents finite_map list gasSummary
  fragGasMode fragGasPathMem gasExemptCert vyperEvalPreservesScopes
  vyperStorageFootprint fragExec bodyPtrDefs
  stmtSimForParts stmtSimForRange gasShadow allocLimits bodySim compileVyper
  gasContext vyperTypeSystem supportedStmts vyperTypeCallGraph
  vyperTypeCallStackSoundness supportedStmtTraverse

val _ = Parse.hide "body";

Theorem for_imm_body_fragment_normalized_full:
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ bc
    (stmts_env bc lctx ret_ty stmts)
    (stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts)) source ee /\
  stmts_env bc lctx ret_ty stmts sb0 = (bc_out,sb1) /\
  stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts) shadow_sb0 =
    (bc_out,shadow_sb1) /\
  gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sb0 sb1 func /\ fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ret_pc_ok bc sb0 sstart /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sb0 x) /\ ~block_is_terminated sb0 /\
  gas_admissible source (stmt_res_ok lctx) ee /\
  return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func bc cx ee sstart /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d bc cx ee Gstart tnstart sstart) /\
  ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
  sstart.vs_inst_idx = LENGTH sb0.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 source (ee,sstart,Gstart,tnstart)
    (\H res mid G tn t. mid.gas_obs = [] /\ ?cenv''.
      stmt_lands lctx sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      sstart.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G tn t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sb0 x ==>
        FLOOKUP G x = FLOOKUP Gstart x /\
        op_taint tn (Var x) = op_taint tnstart (Var x)))
    (\H res mid gt r.
      (!tail. stmt_exit_ptr (RetQ H) (mid with gas_obs := tail) res gt r) /\
      halt_exit H cx mid res r /\
      (ctx_has_dalloca ctx ==> !s.
        (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_full_def] >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (qspecl_then [`st0`,`sstart`,`Gstart`,`tnstart`] mp_tac) >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      drule_all contextRawReachableTheory.frag_reachable_members >>
      qpat_x_assum `~ctx_has_dalloca ctx` mp_tac >>
      simp[ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM,
           unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[]) >>
  strip_tac >>
  drule gas_outcome_full_post_source >>
  disch_then irule >> simp[]
QED

Theorem for_imm_handled_round_bad_storage:
  gas_bad_storage_at cx st0 (eval_stmts cx body)
    ((es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv;
                        value := v; popped := []|>)) :: es.scopes)
     with gas_obs := []) s marks /\
  ~s.vs_halted ==>
  gas_bad_storage_at cx st0
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od) es s marks
Proof
  strip_tac >>
  `gas_marked_exec T (ARB,ARB) (push_scope_with_var id tv v)
     (es,s) [] (INL ())
     (es with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv;
                         value := v; popped := []|>)) :: es.scopes) (OK s)` by
    (simp[gas_marked_exec_def, push_scope_with_var_def, return_def,
          evaluation_state_component_equality] >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  rewrite_tac[ignore_bind_def] >>
  `marks = [] ++ marks` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_bad_storage_at_bind_right >>
  first_assum (irule_at Any) >> simp[] >>
  rewrite_tac[GSYM ignore_bind_def] >>
  irule array_body_cleanup_bad >>
  `!st gs scs. st with <|gas_obs := gs; scopes := scs|> =
                st with <|scopes := scs; gas_obs := gs|>` by
    simp[evaluation_state_component_equality] >>
  metis_tac[]
QED

Theorem for_imm_handled_round_source:
  (!tail. eval_stmts cx body
     ((es with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv;
                         value := v; popped := []|>)) :: es.scopes)
      with gas_obs := obs ++ tail) = (res, ee with gas_obs := tail)) /\
  ee.scopes = sc :: rest ==>
  !tail.
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od)
      (es with gas_obs := obs ++ tail) =
    ((case res of INL u => INL F
      | INR e => if e = ContinueException then INL F
                 else if e = BreakException then INL T else INR e),
     (ee with scopes := rest) with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  `!st. st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tv;
                              value := v; popped := []|>)) =
     st with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv;
                         value := v; popped := []|>)) :: st.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[push_scope_with_var_def, ignore_bind_def, bind_def, return_def] >>
  `!st gs scs. st with <|scopes := scs; gas_obs := gs|> =
                st with <|gas_obs := gs; scopes := scs|>` by
    simp[evaluation_state_component_equality] >>
  qpat_x_assum `!st gs scs. _` (fn th => pure_once_rewrite_tac[th]) >>
  simp[finally_def, try_def, ignore_bind_def, bind_def, return_def,
       handle_loop_exception_def] >>
  Cases_on `res`
  >- simp[ignore_bind_def, bind_def, pop_scope_def, return_def,
          evaluation_state_component_equality] >>
  rename1 `INR err` >> Cases_on `err` >>
  simp[ignore_bind_def, bind_def, pop_scope_def, return_def, raise_def,
       evaluation_state_component_equality]
QED

Theorem for_imm_handled_round_certificate:
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_stmts cx body) (return ()))
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv;
                        value := v; popped := []|>)) :: es.scopes,s)
    marks (err,ee) (leaf,finish_state) /\ ~s.vs_halted ==>
  ?ee'. gas_exempt_cert T tops (ctx,func)
    (ignore_bind
      (do push_scope_with_var id tv v;
          finally (try (do eval_stmts cx body; return F od)
                       handle_loop_exception) pop_scope od) (return ()))
    (es,s) marks (err,ee') (leaf,finish_state)
Proof
  strip_tac >>
  `ee.scopes <> []` by
    (drule gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def] >>
     Cases_on `eval_stmts cx body
       ((es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tv;
                           value := v; popped := []|>)) :: es.scopes)
        with gas_obs := gas_explicit marks s.vs_gas_readings)` >>
     rename1 `_ = (res,st)` >> Cases_on `res` >> simp[] >> strip_tac >>
     gvs[] >> drule eval_stmts_preserves_scopes_len >> simp[] >>
     strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  Cases_on `ee.scopes` >> gvs[] >>
  qexists_tac `ee with scopes := t` >>
  irule for_round_cert >> simp[] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem for_imm_handled_round_full:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx body)
    (((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := []),s,G,tn)
    B (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s.
        (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)) /\
  ~s.vs_halted /\
  (!res ee G1 tn1 t gs.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      B H res ee G1 tn1 t) /\
    eval_stmts cx body
      ((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := gs) = (res,ee) ==>
    (res = INL () \/ res = INR BreakException \/
     res = INR ContinueException) /\
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK u,G2,tn2) /\
      Q H (INL (res = INR BreakException))
        (ee with scopes := TL ee.scopes) G2 tn2 u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od)
    (es,s,G,tn) Q
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !s.
        (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule (INST_TYPE [beta |-> ``:bool``]
    gas_outcome_full_handler_transport) >>
  disch_then irule >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `err` >>
      irule for_imm_handled_round_certificate >> simp[] >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule for_imm_handled_round_bad_storage >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `!tail. eval_stmts cx body
     ((es with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv;
                         value := v; popped := []|>)) :: es.scopes)
      with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
     (res,ee with gas_obs := tail)` by simp[] >>
  `ee.scopes <> []` by
    (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
     drule eval_stmts_preserves_scopes_len >> simp[] >>
     strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  Cases_on `?t. r = OK t`
  >- (pop_assum strip_assume_tac >> gvs[exit_result_def] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
        B H res (ee with gas_obs := []) G' tn' t` by metis_tac[] >>
      qpat_x_assum `!res' ee' G1 tn1 t gs. _`
        (qspecl_then [`res`, `ee with gas_obs := []`] mp_tac) >>
      simp[] >> disch_then drule >>
      disch_then (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
      impl_tac >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
      disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
      qexistsl_tac [`marks`, `INL (res = INR BreakException)`,
        `ee with scopes := TL ee.scopes`, `OK u`, `G2`, `tn2`] >>
      simp[exit_result_def] >> conj_tac
      >- (Cases_on `ee.scopes` >> gvs[] >>
          drule_at (Pos last) for_imm_handled_round_source >> simp[] >>
          disch_then drule >> simp[]) >>
      gen_tac >> strip_tac >>
      `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_origin_ptr_path_append >> metis_tac[]) >>
  `!H tail. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res (G',tn') r`
    by metis_tac[] >>
  `res <> INL () /\ res <> INR BreakException /\
   res <> INR ContinueException` by
    (qpat_x_assum `!H tail. _`
       (qspecl_then [`storage_trace_horizon ee.storage_trace`, `[]`] mp_tac) >>
     simp[stmt_exit_ptr_def] >> rpt strip_tac >>
     Cases_on `r` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
  Cases_on `res` >> gvs[] >>
  rename1 `INR ex` >>
  qexistsl_tac [`marks`, `INR ex`, `ee with scopes := TL ee.scopes`,
    `r`, `G'`, `tn'`] >> simp[] >> conj_tac
  >- (Cases_on `ee.scopes` >> gvs[] >>
      drule_at (Pos last) for_imm_handled_round_source >> simp[] >>
      disch_then drule >> simp[]) >>
  rpt strip_tac
  >- (qpat_x_assum `!H tail. _` (qspecl_then [`H`, `tail`] mp_tac) >>
      simp[stmt_exit_ptr_def, NoAsms] >> metis_tac[])
  >- (gvs[exprSimDefsTheory.halt_exit_def,
          loweringStateRelDefsTheory.halt_rel_def,
          loweringStateRelDefsTheory.accounts_rel_def]) >>
  metis_tac[]
QED

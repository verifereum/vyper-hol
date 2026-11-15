(* For-specific source and joint round boundaries.  The selected body
   execution is retained through handler cleanup; no independent legacy
   target execution is used. *)
Theory bodyFullForRounds
Ancestors
  gasOutcomeFullStmts gasOutcomeFullCompose stmtForRangeMemoryRound
  stmtSimForArrayLoop stmtSimDefs stmtSimForRounds
  fragGasOriginPtr vyperInterpreter vyperState vyperStorageTrace
  gasStorage gasEvents finite_map list gasSummary fragGasMode fragGasPathMem
  gasExemptCert vyperEvalPreservesScopes vyperStorageFootprint fragExec bodyPtrDefs

val _ = Parse.hide "body";

Theorem for_handled_round_bad_storage[local]:
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

Theorem for_handled_round_source[local]:
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

Theorem for_handled_round_certificate[local]:
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

Theorem for_handled_round_full:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx body)
    (((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := []),s,G,tn)
    B (\H res ee gt r. !tail.
      stmt_exit (RetQ H) (ee with gas_obs := tail) res r) /\
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
      !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) (INR ex) r)
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
      irule for_handled_round_certificate >> simp[] >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule for_handled_round_bad_storage >> simp[]) >>
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
          drule_at (Pos last) for_handled_round_source >> simp[] >>
          disch_then drule >> simp[]) >>
      gen_tac >> strip_tac >>
      `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_origin_ptr_path_append >> metis_tac[]) >>
  `!H tail. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_exit (RetQ H) (ee with gas_obs := tail) res r` by metis_tac[] >>
  `res <> INL () /\ res <> INR BreakException /\
   res <> INR ContinueException` by metis_tac[stmt_exit_loop_ctl] >>
  Cases_on `res` >> gvs[] >>
  rename1 `INR ex` >>
  qexistsl_tac [`marks`, `INR ex`, `ee with scopes := TL ee.scopes`,
    `r`, `G'`, `tn'`] >> simp[] >> conj_tac
  >- (Cases_on `ee.scopes` >> gvs[] >>
      drule_at (Pos last) for_handled_round_source >> simp[] >>
      disch_then drule >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!H tail. _` (qspecl_then [`H`, `tail`] mp_tac) >>
  simp[stmt_exit_def, NoAsms] >> metis_tac[]
QED

Theorem eval_for_rounds_full:
  (!a. round a =
    (do v <- read_result cx a;
        push_scope_with_var nm tyv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od)) /\
  (!rs b. next rs b =
    if b then return () else eval_for cx tyv nm body rs) /\
  (!a rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         Inv H (a::rs) es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (a::rs)) ok es ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (round a) (es,s,G,tn)
      (\H res ee G1 tn1 t.
        ee.gas_obs = [] /\ ~t.vs_halted /\
        ?b. res = INL b /\
          (b ==> Done H ee G1 tn1 t) /\
          (~b ==> Inv H rs ee G1 tn1 t))
      (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) /\
  (!es s G tn.
    ~s.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         Inv H [] es G tn s) /\
    gas_admissible (eval_for cx tyv nm body []) ok es ==>
    ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G1,tn1) /\
      Done H (es with gas_obs := []) G1 tn1 t) /\
  (!a rs es s marks err ee leaf stop_state.
    gas_exempt_cert T tops (ctx,func)
      (ignore_bind (round a) (return ()))
      (es,s) marks (err,ee) (leaf,stop_state) ==>
    gas_exempt_cert T tops (ctx,func)
      (bind (round a) (\b. ignore_bind (next rs b) (return ())))
      (es,s) marks (err,ee) (leaf,stop_state)) /\
  (!a rs es s left b mid t right err ee leaf stop_state.
    gas_marked_exec T (ctx,func) (round a) (es,s)
      left (INL b) mid (OK t) /\
    gas_exempt_cert T tops (ctx,func)
      (ignore_bind (next rs b) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,stop_state) ==>
    gas_exempt_cert T tops (ctx,func)
      (bind (round a) (\b. ignore_bind (next rs b) (return ())))
      (es,s) (left ++ right) (err,ee) (leaf,stop_state)) ==>
  !rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         Inv H rs es G tn s) /\
    gas_admissible (eval_for cx tyv nm body rs) ok es ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (eval_for cx tyv nm body rs) (es,s,G,tn)
      (\H res ee G1 tn1 t. res = INL () /\ Done H ee G1 tn1 t)
      (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >> Induct_on `rs` >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac
  >- suspend "nil" >> suspend "cons"
QED

Resume eval_for_rounds_full[nil]:
  qpat_x_assum `!es s G tn. _` (drule_all_then strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G1`, `es`, `[]`, `OK t`, `INL ()`, `tn1`] >>
  simp[Once evaluate_def, return_def, gas_explicit_def]
QED

Resume eval_for_rounds_full[cons]:
  `eval_for cx tyv nm body (h::rs) = bind (round h) (next rs)` by
    (rewrite_tac[eval_for_cons_round] >>
     BINOP_TAC >- simp[] >> simp[FUN_EQ_THM]) >>
  pop_assum (fn th => assume_tac th >> rewrite_tac[th]) >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- (gen_tac >> simp[storage_trace_frame_cond,
    storage_trace_frame_return, evaluate_storage_trace_frame]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (simp[] >>
    irule storage_trace_frame_bind_all >>
    simp[evaluate_storage_trace_frame, storage_trace_frame_ignore_bind,
      storage_trace_frame_state_updates, storage_trace_frame_finally,
      storage_trace_frame_pop_scope, storage_trace_frame_try,
      storage_trace_frame_return, storage_trace_frame_loop_handler,
      storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G1 tn1 t.
    ee.gas_obs = [] /\ ~t.vs_halted /\
    ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
        (~b ==> Inv H rs ee G1 tn1 t)` >>
  reverse conj_tac
  >- (qpat_x_assum `!a rs es s G tn. _`
        (drule_all_then mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
  `mid.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b` by metis_tac[] >>
  gvs[] >>
  `gas_admissible (next rs b) ok mid` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  Cases_on `b` >> gvs[]
  >- (irule gas_outcome_full_intro >>
      qexistsl_tac [`G1`, `mid`, `[]`, `OK t`, `INL ()`, `tn1`] >>
      simp[return_def, gas_explicit_def, gas_origin_ptr_path_rules] >>
      qpat_x_assum `mid.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >>
      simp[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise eval_for_rounds_full

Theorem for_handled_round_ptr_full:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx body)
    (((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := []),s,G,tn)
    B (\H res ee gt r. !tail.
      stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
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
      !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r)
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
      irule for_handled_round_certificate >> simp[] >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule for_handled_round_bad_storage >> simp[]) >>
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
          drule_at (Pos last) for_handled_round_source >> simp[] >>
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
      drule_at (Pos last) for_handled_round_source >> simp[] >>
      disch_then drule >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!H tail. _` (qspecl_then [`H`, `tail`] mp_tac) >>
  simp[stmt_exit_ptr_def, NoAsms] >> metis_tac[]
QED

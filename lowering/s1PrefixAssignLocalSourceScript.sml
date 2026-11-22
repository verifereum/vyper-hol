(* Request-prefix companion to bodyFullAssignLocalSource. *)
Theory s1PrefixAssignLocalSource
Ancestors
  s1PrefixPreds bodyFullAssignLocalSource s1PrefixDefs tuplePlaceStep
  stmtSimAssignSource vyperState

Theorem body_assign_local_word_prefix_source:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q1
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn) /\
  (!marks res mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      Q1 H res (mid with gas_obs := []) G1 tn1 t) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (es,s,G,tn) Q R) /\
  (!marks res mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      Q1 H res (mid with gas_obs := []) G1 tn1 t) ==>
       gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (es,s,G,tn)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (es,s,G,tn)
Proof
  strip_tac >> drule assign_local_admissible_run >> strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _`
    (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC) o
     REWRITE_RULE[gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  qabbrev_tac `gs = gas_explicit marks s.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `_ = (rhs,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `bind _ (write_place _ _) _ = _` mp_tac >>
     Cases_on `rhs` >> simp[Once bind_def] >>
     metis_tac[write_place_storage_trace]) >>
  simp[] >> qexistsl [`mid`, `rhs`, `sfx`, `tail`] >>
  fs[Abbr `gs`]
QED

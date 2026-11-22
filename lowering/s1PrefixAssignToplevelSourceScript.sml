(* Request-prefix companion to bodyFullAssignToplevelSource. *)
Theory s1PrefixAssignToplevelSource
Ancestors
  s1PrefixPreds bodyFullAssignToplevelSource s1PrefixDefs

Theorem body_assign_toplevel_word_prefix_source:
  gasContext$gas_admissible (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
    (stmtSimDefs$stmt_res_ok lctx) es /\
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
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
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
      cx st0 (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (es,s,G,tn)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (es,s,G,tn)
Proof
  cheat
QED

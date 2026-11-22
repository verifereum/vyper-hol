(* Request-prefix companion to bodyFullUnaryValueCompose. *)
Theory s1PrefixUnaryValueCompose
Ancestors
  s1PrefixPreds bodyFullUnaryValueCompose s1PrefixDefs

Theorem gas_outcome_prefix_unary_value:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) childQ childR /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn) /\
  (!H res ee HG tm t. childQ H res ee HG tm t ==> ?v. res = INL v) /\
  (!H res ee gt r. childR H res ee gt r ==>
    ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks res mid HG tm t v.
    res = INL v /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H res mid HG tm t) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (next v) (mid,t,HG,tm) Q R) /\
  (!marks res mid HG tm t v.
    res = INL v /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H res mid HG tm t) ==>
       gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (next v)
      (mid,t,HG,tm)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next)
      (es,s,G,tn)
Proof
  cheat
QED

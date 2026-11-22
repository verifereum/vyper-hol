(* Request-prefix companion to bodyFullForRounds. *)
Theory s1PrefixForRounds
Ancestors
  s1PrefixPreds bodyFullForRounds s1PrefixDefs

val _ = Parse.hide "body";

Theorem eval_for_rounds_prefix:
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
      (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r) /\
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (round a) (es,s,G,tn)) ==>
  !rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         Inv H rs es G tn s) /\
    gas_admissible (eval_for cx tyv nm body rs) ok es ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (eval_for cx tyv nm body rs) (es,s,G,tn)
Proof
  cheat
QED

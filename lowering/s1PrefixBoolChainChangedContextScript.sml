(* Compose at a native midpoint where the source call stack has changed. *)
Theory s1PrefixBoolChainChangedContext
Ancestors
  s1PrefixCompose s1PrefixIntCallArgsSource

Theorem bool_chain_bind_changed_context_prefix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 left
    (es,s,G,tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 left (es,s,G,tn) /\
  (!marks v mid G1 tn1 t.
     (!tail. left (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
             (INL v, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1) /\
       Q1 H (INL v) mid G1 tn1 t) ==>
     ?key entered right.
       mid.storage_trace = entered.storage_trace /\ mid.requests = entered.requests /\
       (!tail. next v (mid with gas_obs := tail) = right (entered with gas_obs := tail)) /\
       gas_prefix_full (DF,lo,explicit,ctx,func,PG) (cx with stk updated_by CONS key)
         st0 right (entered,t,G1,tn1)) /\
  storage_trace_frame left /\ (!v. storage_trace_frame (next v)) /\
  requests_outcomes_frame left ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (bind left next) (es,s,G,tn)
Proof
  strip_tac >> irule gas_prefix_full_bind_replay >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Q1`,`R1`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  qpat_assum `!marks v mid G1 tn1 t. _ ==> ?key entered right. _`
    (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[intcall_args_prefix_stack] >> strip_tac >>
  drule_all intcall_args_prefix_source_replay >> simp[]
QED

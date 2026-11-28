(* A widened tuple's detached snapshot is carried to the next store cursor. *)
Theory s1PrefixTupleWidenedStore
Ancestors
  tupleWidenedStoreEntry s1PrefixTupleStoreList s1PrefixDefs gasOutcomeFull
  gasStorage bodyFullExtCallPackingReady vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState list
  bodyInvCodeProps[qualified] contractInvContextProps[qualified] bodyFullPredsMods[qualified]

Theorem tuple_store_head_bad_domain[local]:
  ~s.vs_halted /\ ~storage_trace_domain cx st0 src.storage_trace ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (assign_tuple_targets cx g v) (src,s,G,tn) Q R /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (assign_tuple_targets cx g v) (src,s,G,tn)
Proof
  strip_tac >> conj_tac
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_bad_storage_at_initial,evaluate_storage_trace_frame] >>
      metis_tac[gas_origin_ptr_focus_nil]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- metis_tac[gas_origin_ptr_focus_nil] >>
  rpt gen_tac >> strip_tac >>
  `storage_trace_domain cx st0 obs_pre` by metis_tac[extcall_packing_observed_domain] >>
  `storage_trace_frame (assign_tuple_targets cx g v)` by
    simp[evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> strip_tac >> fs[] >>
  `TAKE (LENGTH (src:evaluation_state).storage_trace) obs_pre = src.storage_trace` by
    (qpat_assum `APPEND _ _ = APPEND _ _`
       (mp_tac o Q.AP_TERM `TAKE (LENGTH (src:evaluation_state).storage_trace)`) >>
     simp[GSYM APPEND_ASSOC,TAKE_APPEND1]) >>
  metis_tac[TAKE_DROP,storage_trace_domain_prefix]
QED

Theorem tuple_store_widened_prefix_from_heads:
  body_inv tops ctx cenv cx /\ LENGTH gs = LENGTH vs /\
  tuple_widened_store_entry [] (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
    (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf) i c sh src s G tn obs /\
  body_tuple_targets_prefix_ok cx (DROP i gs) (DROP i vs) /\
  gas_admissible (assign_tuple_target_list cx (DROP i gs) (DROP i vs)) ok src /\
  (!j c0 sh0 src0 s1 G1 tn1 obs0.
    j < LENGTH gs /\
    tuple_widened_store_entry [] (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
      (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf) j c0 sh0 src0 s1 G1 tn1 obs0 /\
    gas_admissible (assign_tuple_target_list cx (DROP j gs) (DROP j vs)) ok src0 /\
    body_tuple_target_full_ok cx (EL j gs) (EL j vs) /\
    body_tuple_target_prefix_ok cx (EL j gs) (EL j vs) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (assign_tuple_targets cx (EL j gs) (EL j vs)) (src0,s1,G1,tn1)
      (\H res mid G2 tn2 s2. ?c2 sh2 obs2.
        tuple_widened_store_entry [] (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
          (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf)
          (SUC j) c2 sh2 mid s2 G2 tn2 obs2)
      (\H res ee gt r. ISR res) /\
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (assign_tuple_targets cx (EL j gs) (EL j vs)) (src0,s1,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (assign_tuple_target_list cx (DROP i gs) (DROP i vs)) (src,s,G,tn)
Proof
  strip_tac >>
  qpat_assum `tuple_widened_store_entry _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE[tuple_widened_store_entry_def]) >>
  `cenv.ce_modules = [(NONE,tops)] /\
    ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (drule_then (fn inv => ACCEPT_TAC (CONJ
      (MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules inv)
      (MATCH_MP contractInvContextPropsTheory.contract_inv_singleton_source_modules inv)))
      bodySimTheory.body_inv_contract) >>
  `body_tuple_targets_full_ok cx (DROP i gs) (DROP i vs)` by
    fs[bodyFullPredsModsTheory.body_tuple_target_full_ok_mods_singleton] >>
  qabbrev_tac `entry = tuple_widened_store_entry []
    (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
    (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf)` >>
  irule tuple_store_list_guarded_prefix >> simp[] >>
  qexistsl_tac [`\H todo vals src s G tn.
     ?j c sh obs. todo = DROP j gs /\ vals = DROP j vs /\ entry j c sh src s G tn obs`,
     `ok`, `tops`] >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  map_every qx_gen_tac [`g`,`rest`,`v`,`vals`,`src0`,`s1`,`G1`,`tn1`] >> strip_tac >>
  qexists_tac `\H res ee gt r. ISR res` >> simp[] >>
  Cases_on `storage_trace_domain cx st0 src0.storage_trace`
  >- ( `valid_horizon cx st0 (storage_trace_horizon src0.storage_trace) src0.storage_trace`
         by fs[storage_trace_domain_def] >>
       first_x_assum (drule_then strip_assume_tac) >>
       qpat_assum `_ = DROP j gs`
         (strip_assume_tac o MATCH_MP fragExecTheory.DROP_EQ_CONS o SYM) >>
       qpat_assum `_ = DROP j vs`
         (strip_assume_tac o MATCH_MP fragExecTheory.DROP_EQ_CONS o SYM) >>
       `gas_admissible (assign_tuple_target_list cx (DROP j gs) (DROP j vs)) ok src0`
         by metis_tac[] >>
       qpat_assum `!j c0 sh0 src0 s1 G1 tn1 obs0. _`
         (qspec_then `j` mp_tac) >>
       simp[] >> disch_then (drule_all_then strip_assume_tac) >> simp[] >>
       qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
         (mp_then Any irule gas_outcome_full_post_mono) >> simp[] >>
       rpt strip_tac
       >- fs[Abbr `entry`,tuple_widened_store_entry_def]
       >- fs[Abbr `entry`,tuple_widened_store_entry_def] >>
       qexists_tac `SUC j` >> simp[] >> metis_tac[]) >>
  irule tuple_store_head_bad_domain >> simp[]
QED

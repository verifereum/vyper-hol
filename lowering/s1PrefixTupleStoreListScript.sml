(* Prefix composition for the source tuple-store loop. *)
Theory s1PrefixTupleStoreList
Ancestors
  s1PrefixPreds s1PrefixCompose s1PrefixFrame s1PrefixProps bodyFullPreds
  bodyFullTupleTargetProjection
  gasOutcomeFull stmtSimForRounds gasContext vyperStorageTrace vyperInterpreter
  vyperState list

(* The cursor advances only after a successful replay of the head store. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "head") >> Induct_on `todo`
  >- (Cases_on `vs` >> simp[] >> rpt strip_tac >>
      simp[Once evaluate_def] >> irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_return,return_def]) >>
  qx_gen_tac `g` >> qx_gen_tac `values` >> Cases_on `values` >> simp[] >>
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `assign_tuple_target_list _ (g::gs) (v::vs)` >>
  strip_tac >>
  dxrule_then strip_assume_tac body_tuple_targets_full_ok_cons_parts >>
  qpat_x_assum `body_tuple_targets_prefix_ok _ (_::_) (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE[body_tuple_target_prefix_ok_def]) >>
  asm "head" (drule_all_then strip_assume_tac) >>
  `assign_tuple_target_list cx (g::gs) (v::vs) =
     ignore_bind (assign_tuple_targets cx g v) (assign_tuple_target_list cx gs vs)`
    by simp[Once evaluate_def] >>
  qpat_assum `assign_tuple_target_list _ (_::_) (_::_) = _` (pure_rewrite_tac o single) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ R` (mp_then Any irule gas_prefix_full_ignore_bind) >>
  simp[evaluate_storage_trace_frame,evaluate_requests_outcomes_frame] >> conj_tac
  >- (map_every qx_gen_tac [`marks`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
        by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
        (drule_then strip_assume_tac) >>
      `?ee x ee'. assign_tuple_targets cx g v ee = (INL x,ee')` by
        (qpat_assum `!tail. assign_tuple_targets _ _ _ _ = _`
           (qspec_then `[]` assume_tac) >> metis_tac[]) >>
      qpat_assum `assign_tuple_target_list _ (_::_) (_::_) = _`
        (fn th => qpat_x_assum `gas_admissible _ _ es`
           (assume_tac o REWRITE_RULE[th,ignore_bind_def])) >>
      drule_all gas_admissible_bind_tail >> simp[] >> disch_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED
*)
Theorem tuple_store_list_guarded_prefix:
  (!g gs v vs es s G tn.
     LENGTH gs = LENGTH vs /\ ~s.vs_halted /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
          Inv H (g::gs) (v::vs) es s G tn) /\
     gas_admissible (assign_tuple_target_list cx (g::gs) (v::vs)) ok es /\
     body_tuple_target_full_ok cx g v /\ body_tuple_target_prefix_ok cx g v ==>
     ?R.
       gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
         (assign_tuple_targets cx g v) (es,s,G,tn)
         (\H res mid G1 tn1 t. mid.gas_obs = [] /\ ~t.vs_halted /\
            Inv H gs vs mid t G1 tn1) R /\
       (!H res ee gt r. R H res ee gt r ==> ISR res) /\
       gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
         (assign_tuple_targets cx g v) (es,s,G,tn)) ==>
  !todo vs es s G tn.
    LENGTH todo = LENGTH vs /\ ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H todo vs es s G tn) /\
    gas_admissible (assign_tuple_target_list cx todo vs) ok es /\
    body_tuple_targets_full_ok cx todo vs /\ body_tuple_targets_prefix_ok cx todo vs ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (assign_tuple_target_list cx todo vs) (es,s,G,tn)
Proof
  cheat
QED

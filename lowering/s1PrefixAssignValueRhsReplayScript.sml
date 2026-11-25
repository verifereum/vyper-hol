(* Replay the raw RHS and its source-only read before entering the target. *)
Theory s1PrefixAssignValueRhsReplay
Ancestors
  s1PrefixCompose s1PrefixProps s1PrefixDefs gasOutcomeFullCompose
  exprSimAggregateSource exprSimMemorySource loweringPosts
  vyperStorageFootprint vyperStorageTrace vyperInterpreter vyperState

Theorem body_assign_raw_read_bind_prefix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_expr cx e) (es,s0,G0,tn0) A B /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_expr cx e) (es,s0,G0,tn0) /\
  (!H res ee G tn s. A H res ee G tn s ==>
    ?tv. res = INL tv /\ vv_post H ctx func cenv cx e es sa sr s0 ee tv vv0 s) /\
  (!H res ee gt r. B H res ee gt r ==> ISR res) /\
  (!marks tv v mid G tn s.
     (!tail. eval_expr cx e
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL tv,mid with gas_obs := tail)) /\
     (!tail. read_result cx tv (mid with gas_obs := tail) =
          (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     mid.gas_obs = [] /\ ~s.vs_halted /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          A H (INL tv) mid G tn s /\
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s0,G0,tn0) marks (OK s,G,tn)) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,s,G,tn)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_expr cx e) (\tv. bind (read_result cx tv)
      (\v. bind (eval_target_place cx t) (\p. write_place cx p v))))
    (es,s0,G0,tn0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
     (eval_expr cx e) (es,s0,G0,tn0)
     (\H res ee G tn s. A H res ee G tn s /\ ee.gas_obs = [] /\ ~s.vs_halted) B` by
    (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[storage_trace_frame_bind_all,storage_trace_frame_read_result,
       evaluate_storage_trace_frame,storage_trace_frame_write_place,
       evaluate_requests_outcomes_frame] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`marks`,`tv`,`mid`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H res ee G tn s. A H res ee G tn s ==> ?tv. _`
    (drule_then strip_assume_tac) >> gvs[] >>
  drule_then (qx_choose_then `v` assume_tac) vv_post_materialises >>
  drule_then assume_tac read_result_gas_obs >>
  `gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
     (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,s,G,tn)` by
    (qpat_assum `!marks tv v mid G tn s. _ ==> gas_prefix_full _ _ _ _ _` irule >>
     simp[] >> qexistsl_tac [`marks`,`tv`] >> simp[]) >>
  `!gs. bind (read_result cx tv)
           (\v. bind (eval_target_place cx t) (\p. write_place cx p v))
           (mid with gas_obs := gs) =
         bind (eval_target_place cx t) (\p. write_place cx p v)
           (mid with gas_obs := gs)` by simp[Once bind_def] >>
  qpat_x_assum `gas_prefix_full _ _ _ (bind (eval_target_place _ _) _) _`
    mp_tac >> simp[gas_prefix_full_def]
QED

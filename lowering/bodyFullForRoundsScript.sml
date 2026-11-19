(* Joint loop induction over the remaining source iterator results. *)
Theory bodyFullForRounds
Ancestors
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr stmtSimForRounds
  vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  gasContext gasSummary gasEvents gasExemptCert gasStorage list

val _ = Parse.hide "body";

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

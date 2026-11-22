(* Request-prefix companion to bodyFullForRounds. *)
Theory s1PrefixForRounds
Ancestors
  s1PrefixCompose s1PrefixFrame s1PrefixProps stmtSimForRounds
  vyperInterpreter vyperState vyperStorageTrace vyperCallOutcomeFrame
  vyperStorageFootprint

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
  strip_tac >> Induct_on `rs` >> rpt gen_tac >> strip_tac
  >- (simp[Once evaluate_def] >> irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_return, return_def]) >>
  `eval_for cx tyv nm body (h::rs) = bind (round h) (next rs)` by
    (rewrite_tac[eval_for_cons_round] >>
     BINOP_TAC >- simp[] >> simp[FUN_EQ_THM]) >>
  (* The empty tail of a singleton loop leaves the round's state unchanged. *)
  `requests_outcomes_frame (round h)` by
    (`!ee. SND (eval_for cx tyv nm body [h] ee) = SND (round h ee)` by
       (gen_tac >> ONCE_REWRITE_TAC[eval_for_cons_round] >>
        qpat_assum `!a. round a = _` (fn th => PURE_ONCE_REWRITE_TAC[GSYM th]) >>
        Cases_on `round h ee` >> rename1 `round h ee = (answer,st)` >>
        Cases_on `answer` >> simp[bind_def, return_def, Once evaluate_def]) >>
     qspecl_then [`cx`, `tyv`, `nm`, `body`, `[h]`] mp_tac
       (cj 4 evaluate_requests_outcomes_frame) >>
     simp[requests_outcomes_frame_def, state_rel_frame_def]) >>
  qpat_x_assum `!a rs es s G tn. _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `eval_for cx tyv nm body (h::rs) = _` SUBST_ALL_TAC >>
  qpat_assum `gas_outcome_full _ _ _ _ (round h) _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >>
  conj_tac
  >- simp[storage_trace_frame_cond, storage_trace_frame_return,
          evaluate_storage_trace_frame] >>
  reverse conj_tac
  >- (simp[] >> conj_tac >- metis_tac[sumTheory.ISR] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_ignore_bind,
        storage_trace_frame_state_updates, storage_trace_frame_finally,
        storage_trace_frame_pop_scope, storage_trace_frame_try,
        storage_trace_frame_return, storage_trace_frame_loop_handler,
        storage_trace_frame_read_result]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  `mid.gas_obs = [] /\ ~t.vs_halted` by metis_tac[] >>
  `gas_admissible (next rs v) ok mid` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  Cases_on `v`
  >- (simp[] >> irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_return, return_def]) >>
  simp[] >> first_x_assum irule >> gvs[]
QED

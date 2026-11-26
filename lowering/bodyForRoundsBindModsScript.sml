(* Compose counted loop rounds on the actual linked path. Inv describes
   the frame with a suffix left to run; Done describes the popped exit frame. *)
Theory bodyForRoundsBindMods
Ancestors
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  fragGasOriginPtr stmtSimForRounds vyperInterpreter vyperState
  vyperStorageTrace vyperStorageFootprint gasContext
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem for_rounds_bind_mods:
  (!a rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         Inv H (a::rs) es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (a::rs)) ok es ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (do v <- read_result cx a;
          push_scope_with_var nm tyv v;
          finally (try (do eval_stmts cx body; return F od)
                       handle_loop_exception) pop_scope od) (es,s,G,tn)
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
      Done H (es with gas_obs := []) G1 tn1 t) ==>
  !rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         Inv H rs es G tn s) /\
    gas_admissible (eval_for cx tyv nm body rs) ok es ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (eval_for cx tyv nm body rs) (es,s,G,tn)
      (\H res ee G1 tn1 t. res = INL () /\ Done H ee G1 tn1 t)
      (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >> Induct_on `rs` >> rpt gen_tac >> strip_tac
  >- suspend "nil" >> suspend "cons"
QED

Resume for_rounds_bind_mods[nil]:
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (qpat_x_assum `!es s G tn. _` (drule_all_then strip_assume_tac) >>
      irule gas_outcome_full_mods_pure >> simp[] >>
      qexistsl_tac [`G1`, `es`, `INL ()`, `t`, `tn1`] >>
      simp[Once evaluate_def, return_def]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[Once evaluate_def, return_def]
QED

Resume for_rounds_bind_mods[cons]:
  qabbrev_tac `round = \a. do v <- read_result cx a;
         push_scope_with_var nm tyv v;
         finally (try (do eval_stmts cx body; return F od)
                      handle_loop_exception) pop_scope od` >>
  qabbrev_tac `next = \b. if b then return () else eval_for cx tyv nm body rs` >>
  `eval_for cx tyv nm body (h::rs) = bind (round h) next` by
    simp[eval_for_cons_round, Abbr `round`, Abbr `next`] >>
  asm_rewrite_tac[] >> irule gas_outcome_full_mods_bind_all >>
  conj_tac >-
    simp[Abbr `next`, storage_trace_frame_cond,
         storage_trace_frame_return, evaluate_storage_trace_frame] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_bool >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_bool >> simp[]) >>
  conj_tac >- (simp[Abbr `round`] >>
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
  >- (simp[Abbr `round`] >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
  `mid.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `gas_admissible (next b) ok mid` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  Cases_on `b` >> gvs[Abbr `next`]
  >- (irule gas_outcome_full_mods_pure >> simp[] >>
      qexistsl_tac [`G1`, `mid`, `INL ()`, `t`, `tn1`] >>
      simp[return_def, gas_origin_ptr_path_rules] >>
      qpat_assum `mid.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Finalise for_rounds_bind_mods

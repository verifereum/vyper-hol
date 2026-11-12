(* A source boundary obstruction, not by itself a full-task counterexample. *)
Theory targetPureWalkOutcomeObstruction
Ancestors
  targetPureWalkProbe gasOutcome exprSimDefs

Theorem raw_log_target_outcome_obstruction:
  ~cx.txn.is_static /\
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = ArrayTV (BaseTV (UintT 256)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [IntV 7]) /\
  (!res ee t. Q res ee t ==> machine_frame es ee) ==>
  ~gas_outcome F tops (ctx,func)
    (eval_base_place cx (SubscriptTarget (NameTarget id) raw_log_index))
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `!gs. eval_base_place cx
      (SubscriptTarget (NameTarget id) raw_log_index)
      (es with gas_obs := gs) =
    (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV 0)])),
     (es with gas_obs := gs) with logs :=
       es.logs ++ [encode_raw_event_values cx.txn.target [] []])` by
    (simp[raw_log_target_execution]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (gvs[gasSummaryTheory.gas_summary_at_def,
           gasSummaryTheory.gas_marked_exec_def] >>
      qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      strip_tac >>
      qpat_x_assum `!res ee t. _` drule >> strip_tac >>
      gvs[vyperMachineFrameTheory.machine_frame_def] >>
      qpat_x_assum `_ = es_end with gas_obs := []`
        (mp_tac o Q.AP_TERM `\(s:evaluation_state). LENGTH s.logs`) >> simp[]) >>
  drule gasExemptCertTheory.gas_exempt_cert_execution >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def]
QED

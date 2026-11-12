(* Packaging a fresh callee frame and saving its restored caller. *)
Theory fmpStageFmpStepsCallPush
Ancestors
  fmpStageRel o1LowerDloadShared ptrDiscipline venomState finite_map

Theorem fmp_stage_call_push:
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function callee.fn_name C'.ctx_functions = SOME callee' /\
  fmp_frame_rel sm fmp0 raw0 (w2n s.vs_fmp) lo lo F
    callee callee' PGc FEMPTY FEMPTY s1 t1 /\
  s1.vs_fmp = s.vs_fmp /\
  s1.vs_memory = s.vs_memory /\ t1.vs_memory = t.vs_memory /\
  s1.vs_call_ctx = s.vs_call_ctx /\ t1.vs_call_ctx = t.vs_call_ctx /\
  s1.vs_accounts = s.vs_accounts /\ t1.vs_accounts = t.vs_accounts /\
  s1.vs_transient = s.vs_transient /\ t1.vs_transient = t.vs_transient /\
  s1.vs_immutables = s.vs_immutables /\ t1.vs_immutables = t.vs_immutables /\
  s1.vs_logs = s.vs_logs /\ t1.vs_logs = t.vs_logs /\
  s1.vs_outcomes = s.vs_outcomes /\ t1.vs_outcomes = t.vs_outcomes /\
  s1.vs_pending_deletions = s.vs_pending_deletions /\
  t1.vs_pending_deletions = t.vs_pending_deletions /\
  s1.vs_gas_readings = s.vs_gas_readings /\
  t1.vs_gas_readings = t.vs_gas_readings /\
  s1.vs_requests = s.vs_requests /\ t1.vs_requests = t.vs_requests /\
  s1.vs_returndata = s.vs_returndata /\ t1.vs_returndata = t.vs_returndata /\
  s1.vs_halted = s.vs_halted /\ t1.vs_halted = t.vs_halted ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F
    (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
        cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    PGc FEMPTY (tn with t_var := FEMPTY) callee s1 lo t1 ((t,lo)::ts)
Proof
  simp[fmp_stage_rel_def, fmp_saved_rel_def,
       fmp_frame_base_def, fmp_frame_lo_def] >>
  rpt strip_tac >>
  gvs[ld_shared_agree_def] >>
  metis_tac[]
QED

Theory createCtorTupleSuccess
Ancestors
  gasOutcome gasSummary gasStorage gasExemptCert exprSimDefs
  vyperInterpreter vyperState vyperStorageFootprint list

(* Successful delayed reading retains the capture endpoint.  In particular,
   this equation does not replace a captured PlaceR by a Value. *)
Theorem ctor_capture_success_bind:
  bind (eval_expr_results cx args)
    (\raws. bind (read_results cx raws) (k raws)) start = (INL z,fin) ==>
  ?raws values mid.
    eval_expr_results cx args start = (INL raws,mid) /\
    read_results cx raws mid = (INL values,mid) /\
    k raws values mid = (INL z,fin)
Proof
  Cases_on `eval_expr_results cx args start` >>
  Cases_on `q` >> simp[bind_def] >>
  rename1 `eval_expr_results cx args start = (INL raws,mid)` >>
  Cases_on `read_results cx raws mid` >>
  Cases_on `q` >> simp[bind_def] >>
  drule read_results_state >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ctor_valid_horizon_domain[local]:
  valid_horizon cx st0 H obs ==> storage_trace_domain cx st0 obs
Proof
  simp[valid_horizon_def, storage_trace_domain_def,
       storage_trace_horizon_def, storage_observations_ok_def,
       regions_consistent_def, storage_locks_separated_def,
       storage_well_formed_on_def, storage_trace_backends_well_formed_def,
       EVERY_MEM] >>
  rpt strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  Cases_on `observation` >> gvs[] >>
  qpat_x_assum `!observation. MEM observation obs ==> _` drule >>
  simp[] >> metis_tac[]
QED

(* The marks belong to the outcome, not to a subsequently chosen successful
   source run.  Only success on this aligned stream yields an OK target path. *)
Theorem ctor_outcome_selected_success:
  gas_outcome F tops (ctx,func) cx st0 source (es,s0) Q
    (\H res ee r. expr_exit res r) ==>
  ?marks. !tail v ee H.
    source (es with gas_obs :=
      gas_explicit marks s0.vs_gas_readings ++ tail) = (INL v,ee) /\
    valid_horizon cx st0 H ee.storage_trace ==>
    ?t. gas_marked_path F ctx func s0 (LENGTH marks) (OK t) /\
        gas_marked_exec F (ctx,func) source (es,s0) marks
          (INL v) (ee with gas_obs := []) (OK t) /\
        Q H (INL v) (ee with gas_obs := []) t /\
        ee.gas_obs = tail
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> rpt strip_tac >>
      gvs[gas_bad_storage_at_def] >>
      qpat_x_assum `!tail. ~storage_trace_domain _ _ _`
        (qspec_then `tail` mp_tac) >>
      simp[] >> metis_tac[ctor_valid_horizon_domain])
  >- (qexists_tac `marks` >>
      gvs[gas_summary_at_def, gas_marked_exec_def] >> rpt strip_tac >>
      qpat_x_assum `!tail. source _ = _`
        (qspec_then `tail` mp_tac) >>
      gvs[] >> simp[gas_marked_exec_def] >> metis_tac[]) >>
  qexists_tac `marks` >> rpt strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qpat_x_assum `!tail. ignore_bind _ _ _ = _`
    (qspec_then `tail` mp_tac) >>
  simp[ignore_bind_def, bind_def, return_def]
QED

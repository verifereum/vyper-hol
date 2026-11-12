(* Finite storage checks use the same gas-selected source execution. A bad
   prefix can finish in the source without aligning the remaining target. *)
Theory gasStorage
Ancestors
  gasSummary gasSummaryCompose fragGasMode vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState list pair

Definition gas_bad_storage_at_def:
  gas_bad_storage_at cx st0 (source : evaluation_state -> 'a evaluation_result)
    es s0 marks <=>
    !tail.
      ~storage_trace_domain cx st0
        (SND (source (es with gas_obs :=
          gas_explicit marks s0.vs_gas_readings ++ tail))).storage_trace
End

Theorem storage_trace_frame_preserves_bad_domain:
  storage_trace_frame f /\ f st = (res,st') /\
  ~storage_trace_domain cx st0 st.storage_trace ==>
  ~storage_trace_domain cx st0 st'.storage_trace
Proof
  rpt strip_tac >> drule_all storage_trace_frame_prefix >> strip_tac >>
  gvs[] >> metis_tac[storage_trace_domain_prefix]
QED

Theorem gas_bad_storage_at_initial:
  storage_trace_frame source /\
  ~storage_trace_domain cx st0 es.storage_trace ==>
  gas_bad_storage_at cx st0 source es s0 marks
Proof
  rw[gas_bad_storage_at_def] >>
  Cases_on `source (es with gas_obs :=
    gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `source _ = (res,ee)` >>
  `~storage_trace_domain cx st0
    (es with gas_obs :=
      gas_explicit marks s0.vs_gas_readings ++ tail).storage_trace` by simp[] >>
  drule_all storage_trace_frame_preserves_bad_domain >> simp[]
QED

Theorem gas_bad_storage_at_bind_left:
  gas_bad_storage_at cx st0 source es s0 marks /\
  (!v. storage_trace_frame (k v)) ==>
  gas_bad_storage_at cx st0 (bind source k) es s0 marks
Proof
  rewrite_tac[gas_bad_storage_at_def] >> strip_tac >> gen_tac >>
  Cases_on `source (es with gas_obs :=
    gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `source _ = (res,ee)` >>
  `~storage_trace_domain cx st0 ee.storage_trace` by
    (first_x_assum (qspec_then `tail` mp_tac) >> simp[]) >>
  Cases_on `res`
  >- (rename1 `source _ = (INL v,ee)` >>
      Cases_on `k v ee` >> simp[bind_def] >>
      metis_tac[storage_trace_frame_preserves_bad_domain]) >>
  simp[bind_def]
QED

Theorem gas_bad_storage_at_counted_prefix:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r /\
  ~storage_trace_domain cx st0 ee.storage_trace ==>
  gas_bad_storage_at cx st0 source es s0 marks
Proof
  simp[gas_marked_exec_def, gas_bad_storage_at_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >> simp[]
QED

Theorem gas_bad_storage_at_bind_right:
  gas_marked_exec memory (ctx,func) source (es,s0) left (INL v) mid (OK t) /\
  gas_bad_storage_at cx st0 (k v) (mid with gas_obs := []) t right ==>
  gas_bad_storage_at cx st0 (bind source k) es s0 (left ++ right)
Proof
  rewrite_tac[gas_marked_exec_def, gas_bad_storage_at_def] >> strip_tac >>
  `gas_explicit (left ++ right) s0.vs_gas_readings =
     gas_explicit left s0.vs_gas_readings ++
     gas_explicit right t.vs_gas_readings` by
    metis_tac[gas_marked_path_exec, gas_explicit_append_path] >>
  gen_tac >>
  qpat_x_assum `!tail. source _ = _`
    (qspec_then `gas_explicit right t.vs_gas_readings ++ tail` assume_tac) >>
  qpat_x_assum `!tail. ~storage_trace_domain _ _ _`
    (qspec_then `tail` mp_tac) >>
  fs[bind_def, APPEND_ASSOC]
QED

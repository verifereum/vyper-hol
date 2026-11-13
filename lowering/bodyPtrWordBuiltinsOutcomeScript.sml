(* Strengthen the normal post on the existing counted pointer-path witness.
   The path premise is a separate obligation, not supplied by a weak post. *)
Theory bodyPtrWordBuiltinsOutcome
Ancestors fragGasPathPtr gasOutcomeMarkedPtr gasSummaryComposePtr

Theorem gas_outcome_ptr_path_strengthen:
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es,s0,G0,tn0) Q R /\
  (!H n G tn t res ee.
    valid_horizon cx st0 H ee.storage_trace /\
    gas_path_ptr (D H) 0 ctx fn PG G0 tn0 s0 n G tn (OK t) /\
    Q H res ee G tn t ==> P H res ee G tn t) ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\ P H res ee G tn t) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >>
  simp[gas_marked_exec_ptr_def] >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!H n G tn t res ee. _`
    (qspecl_then [`H`, `LENGTH marks`, `G`, `tn`, `t`, `rr`,
                  `mid with gas_obs := []`] mp_tac) >> simp[]
QED

(* The RHS and operator/write continuation share one joint outcome,
   independently of the target's kind. *)
Theory augAssignFullSource
Ancestors
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr gasExemptCert
  gasSummary gasSummaryCompose vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState vyperAST list

Theorem augassign_rhs_bind_full:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ Qrhs H v ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!marks v mid G1 tn1 t.
     (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Qrhs H v mid G1 tn1 t) ==>
     gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
       (bind (lift_sum (evaluate_binop
         (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
         ptv bop cur v)) (write_place cx p))
       (mid,t,G1,tn1) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur v)) (write_place cx p)))
    (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> fs[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts, storage_trace_frame_write_place]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[] >>
  first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[]
QED

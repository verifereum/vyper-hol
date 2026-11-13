(* One witness connects source readings with memory checks and pointer
   ghosts, including the executed prefix of an exempt source outcome.
   Marks and the one target endpoint come before the finite storage
   horizon; the dead mask is a fixed function DF of that horizon. *)
Theory gasOutcomeFull
Ancestors
  fragGasOriginPtr fragGasOrigin gasOutcome gasStorage gasExemptCert
  gasSummary fragGasMode fragGasPathPtr vyperStorageFootprint
  vyperInterpreter vyperState venomState

Definition gas_outcome_full_def:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
      (es, s, G, tn) Q R <=>
    ?marks.
      gas_bad_storage_at cx st0 source es s marks \/
      (?res ee r G' tn'.
        (!tail.
          source (es with gas_obs :=
                    gas_explicit marks s.vs_gas_readings ++ tail) =
            (res, ee with gas_obs := tail)) /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
            (s, G, tn) marks (r, G', tn') /\
          ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
           (exit_result r /\ R H res (ee with gas_obs := []) (G', tn') r))) \/
      (?err ee leaf leaf_pg leaf_g leaf_tn finish.
        gas_exempt_cert T tops (ctx, func)
          (ignore_bind source (return ()))
          (es, s) marks (err, ee) (leaf, finish) /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
            (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish))
End

(* A horizon valid for a trace is valid for each of its prefixes. *)
Theorem valid_horizon_append:
  valid_horizon cx st0 H (xs ++ ys) ==> valid_horizon cx st0 H xs
Proof
  simp[valid_horizon_def]
QED

Theorem gas_outcome_full_post_mono:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R /\
  (!H res ee G' tn' t. Q H res ee G' tn' t ==> Q' H res ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q' R'
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks` >> metis_tac[]
QED

(* An endpoint whose trace has no intrinsic horizon is a bad-storage prefix. *)
Theorem gas_bad_storage_at_endpoint:
  (!tail.
     source (es with gas_obs :=
               gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, ee with gas_obs := tail)) /\
  ~storage_trace_domain cx st0 ee.storage_trace ==>
  gas_bad_storage_at cx st0 source es s marks
Proof
  simp[gas_bad_storage_at_def]
QED

Theorem gas_outcome_full_memory:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R ==>
  gas_outcome T tops (ctx, func) cx st0 source (es, s)
    (\H res ee t. ?G' tn'. Q H res ee G' tn' t)
    (\H res ee r. ?gt. R H res ee gt r)
Proof
  rw[gas_outcome_full_def, gas_outcome_def] >> qexists_tac `marks`
  >- simp[]
  >- (Cases_on `storage_trace_domain cx st0 ee.storage_trace`
      >- (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
             ee.storage_trace` by fs[storage_trace_domain_def] >>
          first_assum drule >> strip_tac >>
          disj2_tac >> disj1_tac >>
          simp[gas_summary_at_def, gas_marked_exec_def] >>
          qexistsl_tac [`res`, `ee`, `r`] >>
          `gas_marked_path T ctx func s (LENGTH marks) r` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase] >>
          gvs[fragExecTheory.exit_result_def] >>
          TRY disj2_tac >> rpt strip_tac >>
          qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (qspec_then `H` mp_tac) >>
          simp[] >> metis_tac[fragExecTheory.exit_result_def])
      >- (disj1_tac >> irule gas_bad_storage_at_endpoint >> metis_tac[]))
  >- metis_tac[]
QED

Theorem gas_outcome_full_pointer:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R ==>
  gas_outcome_ptr_lo DF lo tops (ctx, func) PG cx st0 source
    (es, s, G, tn) Q R
Proof
  rw[gas_outcome_full_def, gas_outcome_ptr_lo_def,
     gas_summary_ptr_lo_def] >> qexists_tac `marks`
  >- simp[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `G'`, `tn'`, `r`] >>
      metis_tac[gas_origin_ptr_path_projections])
  >> metis_tac[gas_exempt_cert_forget_memory]
QED

(* One witness connects source readings with memory checks and pointer
   ghosts, including the executed prefix of an exempt source outcome. *)
Theory gasOutcomeFull
Ancestors
  fragGasOriginPtr fragGasOrigin gasOutcome gasExemptCert gasSummary fragGasMode
  fragGasPathPtr vyperInterpreter vyperState venomState

Definition gas_outcome_full_def:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
      (es, s, G, tn) Q R <=>
    ?marks.
      (?res ee r G' tn'.
        (!tail.
          source (es with gas_obs :=
                    gas_explicit marks s.vs_gas_readings ++ tail) =
            (res, ee with gas_obs := tail)) /\
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
          (s, G, tn) marks (r, G', tn') /\
        ((?t. r = OK t /\ Q res (ee with gas_obs := []) G' tn' t) \/
         (exit_result r /\ R res (ee with gas_obs := []) (G', tn') r))) \/
      (?err ee leaf leaf_pg leaf_g leaf_tn finish.
        gas_exempt_cert T tops (ctx, func)
          (ignore_bind source (return ()))
          (es, s) marks (err, ee) (leaf, finish) /\
        gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
          (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish))
End

Theorem gas_outcome_full_memory:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R ==>
  gas_outcome T tops (ctx, func) source (es, s)
    (\res ee t. ?G' tn'. Q res ee G' tn' t)
    (\res ee r. ?gt. R res ee gt r)
Proof
  rw[gas_outcome_full_def, gas_outcome_def,
     gas_summary_at_def, gas_marked_exec_def] >>
  metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]
QED

Theorem gas_outcome_full_pointer:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R ==>
  gas_outcome_ptr_lo D lo tops (ctx, func) PG source (es, s, G, tn) Q R
Proof
  rw[gas_outcome_full_def, gas_outcome_ptr_lo_def,
     gas_summary_ptr_lo_def] >>
  metis_tac[gas_origin_ptr_path_projections, gas_exempt_cert_forget_memory]
QED

(* A full counted run may stop at an exempt error in any linked module. *)
Theory gasOutcomeFullMods
Ancestors
  fragGasOriginPtr gasExemptCertMods gasStorage gasSummary
  fragGasPathPtr vyperStorageFootprint vyperInterpreter vyperState venomState

Definition gas_outcome_full_mods_def:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
      (es, s, G, tn) Q R <=>
    ?marks.
      (gas_bad_storage_at cx st0 source es s marks /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         (storage_trace_domain cx st0 es.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace) /\
         gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      (?res ee r G' tn'.
        (!tail.
          source (es with gas_obs :=
                    gas_explicit marks s.vs_gas_readings ++ tail) =
            (res, ee with gas_obs := tail)) /\
        storage_trace_domain cx st0 ee.storage_trace /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
            (s, G, tn) marks (r, G', tn') /\
          ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
           (exit_result r /\ R H res (ee with gas_obs := []) (G', tn') r))) \/
      (?err ee leaf leaf_pg leaf_g leaf_tn finish.
        gas_exempt_cert_mods T mods (ctx, func)
          (ignore_bind source (return ()))
          (es, s) marks (err, ee) (leaf, finish) /\
        ?H. (storage_trace_domain cx st0 es.storage_trace ==>
             valid_horizon cx st0 H es.storage_trace) /\
            gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
              (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish))
End

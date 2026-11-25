(* Decorations constrain the same witnesses as the undecorated outcome.
   In particular, the full decoration and ghost endpoint precede !H. *)
Theory entryCreateOutcomeWitness
Ancestors
  entryCreateCompletedCut gasOutcomeFull

Definition witnessed_operand_outcome_def:
  witnessed_operand_outcome focus full (DF, lo, explicit, ctx, func, PG)
    tops cx st0 source (es, s, G, tn) Q R <=>
    ?marks.
      (gas_bad_storage_at cx st0 source es s marks /\
       focus s marks /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         (storage_trace_domain cx st0 es.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace) /\
         gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      (?res ee r G' tn'.
        full s marks r /\
        (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                 (res, ee with gas_obs := tail)) /\
        storage_trace_domain cx st0 ee.storage_trace /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
            (s, G, tn) marks (r, G', tn') /\
          ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
           (exit_result r /\ R H res (ee with gas_obs := []) (G', tn') r))) \/
      (?err ee leaf leaf_pg leaf_g leaf_tn finish.
        focus s marks /\
        gas_exempt_cert T tops (ctx, func) (ignore_bind source (return ()))
          (es, s) marks (err, ee) (leaf, finish) /\
        ?H. (storage_trace_domain cx st0 es.storage_trace ==>
             valid_horizon cx st0 H es.storage_trace) /\
            gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
              (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish))
End

Theorem witnessed_operand_outcome_unrestricted:
  witnessed_operand_outcome (\s marks. T) (\s marks r. T)
    (DF, lo, explicit, ctx, func, PG) tops cx st0 source (es, s, G, tn) Q R <=>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG)
    tops cx st0 source (es, s, G, tn) Q R
Proof
  simp[witnessed_operand_outcome_def, gas_outcome_full_def]
QED

Theorem witnessed_operand_outcome_scoped:
  witnessed_operand_outcome
    (create_operand_focus_scope sa sb explicit ctx func)
    (create_operand_full_scope sa sb explicit ctx func)
    (DF, lo, explicit, ctx, func, PG) tops cx st0 source (es, s, G, tn) Q R <=>
  scoped_operand_outcome (DF, lo, explicit, ctx, func, PG)
    tops cx st0 sa sb source (es, s, G, tn) Q R
Proof
  simp[witnessed_operand_outcome_def, scoped_operand_outcome_def]
QED

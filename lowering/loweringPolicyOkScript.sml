(* The raw lowering boundary only succeeds on policies inside its contract. *)
Theory loweringPolicyOk
Ancestors vyperCompiler

Theorem run_lowering_policy_ok:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label = SOME unit ==>
  lowering_policy_ok rpolicy
Proof
  Cases_on `lowering_policy_ok rpolicy` >> simp[run_lowering_def]
QED

(* A bad observation is retained by the actual whole source action, for every
   unused source gas suffix. No target execution beyond that observation is needed. *)
Theory gasSourcePrefix
Ancestors
  vyperStorageFootprint vyperState list pair

Definition gas_bad_source_prefix_def:
  gas_bad_source_prefix (cx, initial) action es selected bad_trace <=>
    ~storage_trace_domain cx initial bad_trace /\
    !tail. ?result final rest.
      action (es with gas_obs := selected ++ tail) = (result, final) /\
      final.storage_trace = bad_trace ++ rest
End

Theorem gas_bad_source_prefix_final:
  gas_bad_source_prefix (cx, initial) action es selected bad_trace /\
  action (es with gas_obs := selected ++ tail) = (result, final) ==>
  ~storage_trace_domain cx initial final.storage_trace
Proof
  rw[gas_bad_source_prefix_def] >>
  first_x_assum (qspec_then `tail` strip_assume_tac) >> gvs[] >>
  metis_tac[storage_trace_domain_prefix]
QED

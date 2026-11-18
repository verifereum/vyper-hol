(* Storage checks depend on the call target, not the transaction code. *)
Theory callCodeStorage
Ancestors
  vyperInterpreter vyperStorageFootprint vyperCallFiniteStorageSupport

Theorem call_storage_checks_code_update:
  (storage_well_formed_on
     (initial_evaluation_context am.sources am.layouts (tx with code := c) NONE)
     (initial_state am []) regions /\
   storage_trace_backends_well_formed
     (initial_evaluation_context am.sources am.layouts (tx with code := c) NONE)
     regions obs) <=>
  (storage_well_formed_on
     (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) regions /\
   storage_trace_backends_well_formed
     (initial_evaluation_context am.sources am.layouts tx NONE) regions obs)
Proof
  `!st. storage_well_formed_on
          (initial_evaluation_context am.sources am.layouts (tx with code := c) NONE)
          st regions <=>
        storage_well_formed_on
          (initial_evaluation_context am.sources am.layouts tx NONE) st regions` by
    (gen_tac >> irule storage_well_formed_on_target >>
     simp[initial_evaluation_context_def]) >>
  Induct_on `obs`
  >- simp[storage_trace_backends_well_formed_def] >>
  Cases >> simp[storage_trace_backends_well_formed_def]
QED

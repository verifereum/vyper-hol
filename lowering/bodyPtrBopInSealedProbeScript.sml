(* Entry transport obstruction: a terminal completion of a function cannot
   replace that function in the fixed context required by the S1 boundary.
   This applies even when the replacement entry state is changed. *)
Theory bodyPtrBopInSealedProbe
Ancestors bodyPtrBopInBoundary

Theorem same_context_entry_function_unique:
  stmt_state_rel ctx f cenv cx es s /\
  stmt_state_rel ctx g cenv' cx' es' s' /\
  f.fn_name = g.fn_name ==>
  f = g
Proof
  strip_tac >>
  imp_res_tac stmt_state_rel_context_lookup >> gvs[]
QED

Theorem changed_function_cannot_transport_entry:
  stmt_state_rel ctx f cenv cx es s /\
  f.fn_name = sealed.fn_name /\ f <> sealed ==>
  ~stmt_state_rel ctx sealed cenv' cx' es' s'
Proof
  metis_tac[same_context_entry_function_unique]
QED

(* Execution-side probe for the nonreentrant root boundary.
   The abstract lock fragment does not promise these fields.  They follow
   instead from the exact successful instruction sequence. *)
Theory bodyIntCallNRRootProbe
Ancestors
  transientLockProps venomState

Theorem intcall_transient_lock_run_frame:
  compile_nonreentrant_lock key T view sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_transient := t.vs_transient|>
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  gvs[transient_lock_code_execution, AllCaseEqs()] >>
  gvs[transient_lock_checked_state_def, update_var_def, tstore_def,
      venom_state_component_equality]
QED

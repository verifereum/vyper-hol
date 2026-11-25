(* The executed list at the selected runtime saved-copy endpoint. *)
Theory bodySavedRuntimeCopyPhysical
Ancestors bodyFullExtCallRuntimeCopyReplay

Theorem extcall_saved_runtime_copy_replay_physical:
  ^(concl extcall_saved_runtime_copy_replay_with_run)
Proof
  ACCEPT_TAC extcall_saved_runtime_copy_replay_with_run
QED

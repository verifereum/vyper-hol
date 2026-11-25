(* The accumulator's constructor copy run at the saved replay endpoint. *)
Theory bodySavedCtorCopyPhysical
Ancestors bodyFullExtCallCtorCopyReplay

Theorem extcall_saved_ctor_copy_replay_physical:
  ^(concl extcall_saved_ctor_copy_replay_with_run)
Proof
  ACCEPT_TAC extcall_saved_ctor_copy_replay_with_run
QED

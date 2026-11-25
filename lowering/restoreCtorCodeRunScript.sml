(* The saved constructor restore shares its endpoint and ghosts with the
   physical instruction-list run used by first-exit scope. *)
Theory restoreCtorCodeRun
Ancestors
  bodyFullExtCallCtorCopyReplay

Theorem extcall_saved_ctor_copy_replay_run =
  bodyFullExtCallCtorCopyReplayTheory.extcall_saved_ctor_copy_replay_with_run

(* The saved runtime-code operand and its physical run share one exit. *)
Theory restoreRuntimeCodeRun
Ancestors
  bodyFullExtCallRuntimeCopyReplay

Theorem extcall_saved_runtime_copy_replay_run =
  bodyFullExtCallRuntimeCopyReplayTheory.extcall_saved_runtime_copy_replay_with_run

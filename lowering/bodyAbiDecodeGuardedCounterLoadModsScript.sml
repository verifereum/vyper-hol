Theory bodyAbiDecodeGuardedCounterLoadMods
Ancestors
  bodyAbiDecodeGuardedLoopCounterFrameMods

(* Header-facing compatibility export.  The canonical counter frame is
   proved once by bodyAbiDecodeGuardedLoopCounterFrameMods; retain its exact
   premise, witness scope, and taint-frame fields here without rebuilding the
   MLOAD execution. *)
Theorem abi_decode_loop_counter_load_frame_mods:
  ^(concl abi_decode_loop_counter_load_frame_exact)
Proof
  ACCEPT_TAC abi_decode_loop_counter_load_frame_exact
QED

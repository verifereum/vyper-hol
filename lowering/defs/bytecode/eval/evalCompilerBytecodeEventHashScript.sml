(* A real corpus metadata hash under the unchanged tactic budget. *)
Theory evalCompilerBytecodeEventHash
Ancestors vyperEvent vyperAST finite_map
Libs cv_transLib

val () = cv_trans event_hash_def;

Theorem mixed_event_log_event_hash:
  event_hash FEMPTY "Ping" [BaseT (UintT 256); BaseT (UintT 256)] =
    20237010786485618918152345486277841085958342497490287962008896559846095772078
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

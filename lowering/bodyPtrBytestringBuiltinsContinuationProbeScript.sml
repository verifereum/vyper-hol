Theory bodyPtrBytestringBuiltinsContinuationProbe
Ancestors bodyPtrBytestringBuiltinsTerminalPairProbe
          bodyPtrBytestringBuiltinsConcatRunProbe

(* Concrete continuation observation; no installed-frame assertion is made. *)
Theorem continuation_probe_known_collision:
  DROP 4 (SND (compile_expr terminal_probe_env NoneT terminal_probe_call
    (initial_compile_state ""))).cs_current_insts =
    [mk_inst 4 INVOKE
      [Label "internal 0 sink()_runtime"; Var "%1"; Var "%2"] []]
Proof
  EVAL_TAC
QED

Theorem continuation_probe_concat_fifth:
  EL 4 (SND concat_probe_compiled).cs_current_insts =
    mk_inst 4 MLOAD [Var "%2"] ["%3"]
Proof
  simp[concat_probe_compilation]
QED

Theorem continuation_probe_known_mismatch:
  (EL 4 (SND (compile_expr terminal_probe_env NoneT terminal_probe_call
    (initial_compile_state ""))).cs_current_insts).inst_opcode <>
  (EL 4 (SND concat_probe_compiled).cs_current_insts).inst_opcode
Proof
  simp[continuation_probe_concat_fifth] >> EVAL_TAC
QED

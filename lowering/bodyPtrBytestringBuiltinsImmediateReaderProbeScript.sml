Theory bodyPtrBytestringBuiltinsImmediateReaderProbe
Ancestors bodyPtrBytestringBuiltinsTerminalPairProbe exprLowering compileEnv
          emitHelper venomInst list rich_list

(* The existing load_bytestring_as_word_def is the symbolic continuation
   equation: MLOAD v, ADD v 32, MLOAD data, then SAR-only masking and shifts.
   This boundary states the exact first two emitted records without duplicating
   that full equation. SHR is used by the concrete unsigned conversion below. *)
Theorem immediate_reader_symbolic_prefix:
  !v s. TAKE (LENGTH s.cs_current_insts + 2)
    (SND (load_bytestring_as_word v SHR s)).cs_current_insts =
    s.cs_current_insts ++
      [mk_inst s.cs_next_id MLOAD [v] ["%" ++ toString s.cs_next_var];
       mk_inst (s.cs_next_id + 1) ADD [v; Lit 32w]
         ["%" ++ toString (s.cs_next_var + 1)]]
Proof
  simp[load_bytestring_as_word_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, rich_listTheory.TAKE_APPEND, APPEND_ASSOC] >>
  simp[arithmeticTheory.ADD_SUB, TAKE_LENGTH_TOO_LONG,
       arithmeticTheory.SUB_EQ_0]
QED

(* One closed candidate, preserving the original environment and sink. *)
Definition immediate_reader_convert_def:
  immediate_reader_convert = TypeBuiltin (BaseT (UintT 256)) Convert
    (BaseT (UintT 256)) [terminal_probe_empty]
End
Definition immediate_reader_call_def:
  immediate_reader_call = Call NoneT (IntCall (NONE,"sink"))
    [terminal_probe_expr; immediate_reader_convert] NONE
End

Theorem immediate_reader_supported:
  supported_effect_expr terminal_probe_tops immediate_reader_call
Proof
  EVAL_TAC
QED

Theorem immediate_reader_first_six:
  TAKE 6 (SND (compile_expr terminal_probe_env NoneT immediate_reader_call
    (initial_compile_state ""))).cs_current_insts =
    terminal_probe_final.cs_current_insts ++
      [mk_inst 4 MLOAD [Var "%2"] ["%3"];
       mk_inst 5 ADD [Var "%2"; Lit 32w] ["%4"]]
Proof
  EVAL_TAC
QED

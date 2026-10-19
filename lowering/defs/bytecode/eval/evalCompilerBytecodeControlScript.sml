(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeControl
Ancestors evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

val mixed_event_log_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) mixed_event_log_program``
val () = evalCompilerBytecodeLib.add_compile_eval mixed_event_log_compile_eval

Theorem mixed_event_log_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    mixed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_log.hex")
Proof
  EVAL_TAC
QED

val hashmap_read_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) hashmap_read_program``
val () = evalCompilerBytecodeLib.add_compile_eval hashmap_read_compile_eval

Theorem hashmap_read_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    hashmap_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_read.hex")
Proof
  EVAL_TAC
QED

val hashmap_write_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) hashmap_write_program``
val () = evalCompilerBytecodeLib.add_compile_eval hashmap_write_compile_eval

Theorem hashmap_write_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    hashmap_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_write.hex")
Proof
  EVAL_TAC
QED

val if_bool_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) if_bool_program``
val () = evalCompilerBytecodeLib.add_compile_eval if_bool_compile_eval

Theorem if_bool_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    if_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_bool.hex")
Proof
  EVAL_TAC
QED

val if_join_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) if_join_program``
val () = evalCompilerBytecodeLib.add_compile_eval if_join_compile_eval

Theorem if_join_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    if_join_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_join.hex")
Proof
  EVAL_TAC
QED

(* The checked O1 loop smokes now reach bytecode.  These independent pinned-
 * Python equalities remain exact integration gates; they are not replaced by
 * the successful-compilation expectations in evalCompilerTheory. *)
val for_pass_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) for_pass_program``
val () = evalCompilerBytecodeLib.add_compile_eval for_pass_compile_eval

Theorem for_pass_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_pass_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_pass.hex")
Proof
  EVAL_TAC
QED

val for_accum_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) for_accum_program``
val () = evalCompilerBytecodeLib.add_compile_eval for_accum_compile_eval

Theorem for_accum_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_accum_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_accum.hex")
Proof
  EVAL_TAC
QED

val for_continue_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) for_continue_program``
val () = evalCompilerBytecodeLib.add_compile_eval for_continue_compile_eval

Theorem for_continue_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_continue_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_continue.hex")
Proof
  EVAL_TAC
QED

val for_break_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) for_break_program``
val () = evalCompilerBytecodeLib.add_compile_eval for_break_compile_eval

Theorem for_break_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_break_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_break.hex")
Proof
  EVAL_TAC
QED

(* The scalar entry layout names the hidden return PC with RETPC_PARAM, so
 * checked compilation reaches bytecode. *)
val internal_call_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) internal_call_program``
val () = evalCompilerBytecodeLib.add_compile_eval internal_call_compile_eval

Theorem internal_call_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    internal_call_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call.hex")
Proof
  EVAL_TAC
QED

val internal_call_arg_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities) internal_call_arg_program``
val () = evalCompilerBytecodeLib.add_compile_eval internal_call_arg_compile_eval

Theorem internal_call_arg_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    internal_call_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call_arg.hex")
Proof
  EVAL_TAC
QED

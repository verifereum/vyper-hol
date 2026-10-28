(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeControl
Ancestors evalCompiler compileVyper evalCompilerBytecodeMixedEventStages
  evalCompilerBytecodeControlStages concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/for_accum.hex",
   "../python-o1-no-asm-opt/for_break.hex",
   "../python-o1-no-asm-opt/for_continue.hex",
   "../python-o1-no-asm-opt/for_pass.hex",
   "../python-o1-no-asm-opt/hashmap_read.hex",
   "../python-o1-no-asm-opt/hashmap_write.hex",
   "../python-o1-no-asm-opt/if_bool.hex",
   "../python-o1-no-asm-opt/if_join.hex",
   "../python-o1-no-asm-opt/internal_call.hex",
   "../python-o1-no-asm-opt/internal_call_arg.hex",
   "../python-o1-no-asm-opt/mixed_event_log.hex"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20
val () = evalCompilerBytecodeLib.restore_stage_values "evalCompilerBytecodeMixedEventStages"
val () = app evalCompilerBytecodeLib.restore_stage_values
  ["evalCompilerBytecodeControlHashmapReadStages",
   "evalCompilerBytecodeControlHashmapWriteStages",
   "evalCompilerBytecodeControlIfBoolStages",
   "evalCompilerBytecodeControlIfJoinStages",
   "evalCompilerBytecodeControlForPassStages",
   "evalCompilerBytecodeControlForAccumStages",
   "evalCompilerBytecodeControlForContinueStages",
   "evalCompilerBytecodeControlForBreakStages",
   "evalCompilerBytecodeControlInternalCallStages",
   "evalCompilerBytecodeControlInternalCallArgStages"]

Theorem mixed_event_log_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    mixed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_log.hex")
Proof
  EVAL_TAC
QED

Theorem hashmap_read_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    hashmap_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_read.hex")
Proof
  EVAL_TAC
QED

Theorem hashmap_write_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    hashmap_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_write.hex")
Proof
  EVAL_TAC
QED

Theorem if_bool_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    if_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_bool.hex")
Proof
  EVAL_TAC
QED

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
Theorem for_pass_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_pass_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_pass.hex")
Proof
  EVAL_TAC
QED

Theorem for_accum_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_accum_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_accum.hex")
Proof
  EVAL_TAC
QED

Theorem for_continue_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_continue_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_continue.hex")
Proof
  EVAL_TAC
QED

Theorem for_break_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    for_break_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_break.hex")
Proof
  EVAL_TAC
QED

(* The scalar entry layout names the hidden return PC with RETPC_PARAM, so
 * checked compilation reaches bytecode. *)
Theorem internal_call_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    internal_call_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call.hex")
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    internal_call_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call_arg.hex")
Proof
  EVAL_TAC
QED

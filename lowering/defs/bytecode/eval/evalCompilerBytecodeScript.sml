(*
 * Compiler Bytecode Evaluation Fixtures
 *
 * STATUS: Independent bytecode parity check, not core lowering definitions.
 * Every theorem compares fresh HOL evaluation directly with the independently
 * generated pinned-Python oracle under bytecode/python-o1-no-asm-opt/.  There
 * are no HOL-generated expected outputs.  A bytecode difference or checked HOL
 * rejection therefore fails this theory rather than becoming a new baseline.
 *)

Theory evalCompilerBytecode
Ancestors evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem empty_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ([] : toplevel list) =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "empty.hex")
Proof
  EVAL_TAC
QED

Theorem noop_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    noop_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "noop.hex")
Proof
  EVAL_TAC
QED

Theorem return_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    return_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_uint.hex")
Proof
  EVAL_TAC
QED

Theorem return_arg_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    return_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_arg.hex")
Proof
  EVAL_TAC
QED

Theorem local_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    local_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "local_uint.hex")
Proof
  EVAL_TAC
QED

Theorem add_arg_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    add_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "add_arg.hex")
Proof
  EVAL_TAC
QED

Theorem two_external_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    two_external_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "two_external.hex")
Proof
  EVAL_TAC
QED

Theorem storage_read_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_read.hex")
Proof
  EVAL_TAC
QED

Theorem storage_write_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_write.hex")
Proof
  EVAL_TAC
QED

Theorem deploy_storage_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    deploy_storage_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "deploy_storage.hex")
Proof
  EVAL_TAC
QED

Theorem event_log_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "event_log.hex")
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    indexed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "indexed_event_log.hex")
Proof
  EVAL_TAC
QED

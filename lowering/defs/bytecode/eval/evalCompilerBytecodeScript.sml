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
Libs evalCompilerBytecodeLib compilerClosedFixtureEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/add_arg.hex",
   "../python-o1-no-asm-opt/deploy_storage.hex",
   "../python-o1-no-asm-opt/empty.hex",
   "../python-o1-no-asm-opt/event_log.hex",
   "../python-o1-no-asm-opt/indexed_event_log.hex",
   "../python-o1-no-asm-opt/local_uint.hex",
   "../python-o1-no-asm-opt/noop.hex",
   "../python-o1-no-asm-opt/return_arg.hex",
   "../python-o1-no-asm-opt/return_uint.hex",
   "../python-o1-no-asm-opt/storage_read.hex",
   "../python-o1-no-asm-opt/storage_write.hex",
   "../python-o1-no-asm-opt/two_external.hex"]

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

val () = compilerClosedFixtureEvalLib.cache_compile
  "noop" ``noop_program``

Theorem noop_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    noop_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "noop.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "return_uint" ``return_uint_program``

Theorem return_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    return_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_uint.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "return_arg" ``return_arg_program``

Theorem return_arg_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    return_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_arg.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "local_uint" ``local_uint_program``

Theorem local_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    local_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "local_uint.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "add_arg" ``add_arg_program``

Theorem add_arg_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    add_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "add_arg.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "two_external" ``two_external_program``

Theorem two_external_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    two_external_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "two_external.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_read" ``storage_read_program``

Theorem storage_read_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_read.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_write" ``storage_write_program``

Theorem storage_write_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_write.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "deploy_storage" ``deploy_storage_program``

Theorem deploy_storage_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    deploy_storage_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "deploy_storage.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "event_log" ``event_log_program``

Theorem event_log_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "event_log.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "indexed_event_log" ``indexed_event_log_program``

Theorem indexed_event_log_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    indexed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "indexed_event_log.hex")
Proof
  EVAL_TAC
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("BASELINE_PUBLIC_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "baseline parity has kernel assumptions or admission tags"
end) [("empty_matches_python_oracle",empty_matches_python_oracle),
       ("noop_matches_python_oracle",noop_matches_python_oracle),
       ("return_uint_matches_python_oracle",return_uint_matches_python_oracle),
       ("return_arg_matches_python_oracle",return_arg_matches_python_oracle),
       ("local_uint_matches_python_oracle",local_uint_matches_python_oracle),
       ("add_arg_matches_python_oracle",add_arg_matches_python_oracle),
       ("two_external_matches_python_oracle",two_external_matches_python_oracle),
       ("storage_read_matches_python_oracle",storage_read_matches_python_oracle),
       ("storage_write_matches_python_oracle",storage_write_matches_python_oracle),
       ("deploy_storage_matches_python_oracle",deploy_storage_matches_python_oracle),
       ("event_log_matches_python_oracle",event_log_matches_python_oracle),
       ("indexed_event_log_matches_python_oracle",indexed_event_log_matches_python_oracle)]

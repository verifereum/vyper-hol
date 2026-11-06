Theory evalCompilerEventWidenNestedString
Ancestors eventFixturePrograms compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib eventBytecodeEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../python-event-no-asm-opt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset (computeLib.add_thms [event_widen_nested_string_program_def])

val () = eventBytecodeEvalLib.compile_stages "event_widen_nested_string"
  ``event_widen_nested_string_program``

Theorem event_widen_nested_string_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    event_widen_nested_string_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../python-event-no-asm-opt/event_widen_nested_string.hex")
Proof
  EVAL_TAC
QED

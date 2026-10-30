Theory evalCompilerEventStorageBytes20
Ancestors eventFixturePrograms compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib eventBytecodeEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../python-event-no-asm-opt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset (computeLib.add_thms [event_storage_bytes20_indexed_program_def])

val () = eventBytecodeEvalLib.compile_stages "event_storage_bytes20_indexed"
  ``event_storage_bytes20_indexed_program``

Theorem event_storage_bytes20_indexed_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    event_storage_bytes20_indexed_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../python-event-no-asm-opt/event_storage_bytes20_indexed.hex")
Proof
  EVAL_TAC
QED

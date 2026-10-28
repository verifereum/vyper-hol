Theory evalCompilerEventWidenTuple
Ancestors eventFixturePrograms compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib eventBytecodeEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../python-event-no-asm-opt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset (computeLib.add_thms [event_widen_tuple_program_def])

val () = eventBytecodeEvalLib.compile_stages "event_widen_tuple"
  ``event_widen_tuple_program``

Theorem event_widen_tuple_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    event_widen_tuple_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../python-event-no-asm-opt/event_widen_tuple.hex")
Proof
  EVAL_TAC
QED

val () = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("event parity oracle dependency: " ^ name))
  (DB.thms "evalCompilerEventWidenTuple")

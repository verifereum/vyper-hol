Theory evalCompilerEventForwardStruct
Ancestors eventFixturePrograms compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib eventBytecodeEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../python-event-no-asm-opt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset (computeLib.add_thms [event_forward_struct_program_def])

val () = eventBytecodeEvalLib.compile_stages "event_forward_struct" ``event_forward_struct_program``

Theorem event_forward_struct_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities) event_forward_struct_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../python-event-no-asm-opt/event_forward_struct.hex")
Proof
  EVAL_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed forward-struct parity theorem: " ^ name)
  end) (DB.thms "evalCompilerEventForwardStruct")

Theory evalCompilerEventWidenFixedDynamic
Ancestors eventFixturePrograms compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib eventBytecodeEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../python-event-no-asm-opt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset (computeLib.add_thms [event_widen_fixed_dynamic_program_def])

val () = eventBytecodeEvalLib.compile_stages "event_widen_fixed_dynamic"
  ``event_widen_fixed_dynamic_program``

(* Save the computed result before comparing it with the independent oracle.
   This also keeps a theorem checkpoint across edits to the parity proof. *)
val fixed_dynamic_compilation_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      event_widen_fixed_dynamic_program``

Theorem event_widen_fixed_dynamic_compiler_evaluation:
  ^(concl fixed_dynamic_compilation_eval)
Proof
  ACCEPT_TAC fixed_dynamic_compilation_eval
QED

val () = evalCompilerBytecodeLib.add_compile_eval
  event_widen_fixed_dynamic_compiler_evaluation

Theorem event_widen_fixed_dynamic_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    event_widen_fixed_dynamic_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../python-event-no-asm-opt/event_widen_fixed_dynamic.hex")
Proof
  EVAL_TAC
QED

val () = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("event parity oracle dependency: " ^ name))
  (DB.thms "evalCompilerEventWidenFixedDynamic")

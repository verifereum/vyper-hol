(* Checked source-lowering staging for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEventsLowering
Ancestors evalCompilerSubsetAbiEvents compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val () = computeLib.upd_compset
  (computeLib.add_thms [contextTheory.compile_copy_memory_def])

val mixed_event_types_policy_eval = save_thm
  ("mixed_event_types_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
val mixed_event_types_rpolicy = optionSyntax.dest_some
  (rhs (concl mixed_event_types_policy_eval))
val mixed_event_types_runtime_unit_eval = save_thm
  ("mixed_event_types_runtime_unit_eval",
   EVAL ``lower_vyper_runtime_unit task090_mixed_event_types_program
           ^mixed_event_types_rpolicy``)

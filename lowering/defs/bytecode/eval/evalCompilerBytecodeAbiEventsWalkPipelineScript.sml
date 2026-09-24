(* Checked callee-first pass staging for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEventsWalkPipeline
Ancestors evalCompilerBytecodeAbiEventsPrePipeline evalCompilerBytecodeAbiEventsLowering venomPipelineDriver alist integer_word
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_mixed_event_types,
     word_of_bytes_bytes32_mixed_event_types,
     w2n_mixed_event_types_n2w,
     contextTheory.compile_copy_memory_def])
val () = Globals.max_print_depth := 20

val mixed_event_types_rpolicy = optionSyntax.dest_some
  (rhs (concl mixed_event_types_policy_eval))
val mixed_event_types_pre_pair = optionSyntax.dest_some
  (rhs (concl mixed_event_types_pre_walk_eval))
val mixed_event_types_pre_unit = #1 (pairSyntax.dest_pair mixed_event_types_pre_pair)
val mixed_event_types_pre_supply = #2 (pairSyntax.dest_pair mixed_event_types_pre_pair)
val mixed_event_types_fcg_eval = save_thm
  ("mixed_event_types_fcg_eval",
   EVAL ``fcg_analyze (^mixed_event_types_pre_unit).cu_context``)
val mixed_event_types_fcg = rhs (concl mixed_event_types_fcg_eval)
val mixed_event_types_walk_unit_eval = save_thm
  ("mixed_event_types_walk_unit_eval",
   EVAL ``prune_unit_fcg_unreachable ^mixed_event_types_pre_unit
           ^mixed_event_types_fcg``)
val mixed_event_types_walk_unit = rhs (concl mixed_event_types_walk_unit_eval)
val mixed_event_types_entry = optionSyntax.dest_some (rhs (concl
  (EVAL ``(^mixed_event_types_pre_unit).cu_context.ctx_entry``)))
val mixed_event_types_names_eval = save_thm
  ("mixed_event_types_names_eval",
   EVAL ``fcg_postorder ^mixed_event_types_fcg ^mixed_event_types_entry``)
val mixed_event_types_names = rhs (concl mixed_event_types_names_eval)
val mixed_event_types_walk_eval = save_thm
  ("mixed_event_types_walk_eval",
   EVAL ``run_callee_first ^mixed_event_types_rpolicy o1_fn_passes
           ^mixed_event_types_names ^mixed_event_types_walk_unit
           ^mixed_event_types_pre_supply``)

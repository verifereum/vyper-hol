(* Checked pre-walk pipeline staging for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEventsPrePipeline
Ancestors evalCompilerBytecodeAbiEventsLowering venomPipelineDriver alist integer_word
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
val mixed_event_types_runtime_unit = optionSyntax.dest_some
  (rhs (concl mixed_event_types_runtime_unit_eval))
val mixed_event_types_supply_eval = save_thm
  ("mixed_event_types_supply_eval",
   EVAL ``init_ir_supply ^mixed_event_types_runtime_unit``)
val mixed_event_types_supply = rhs (concl mixed_event_types_supply_eval)
val mixed_event_types_pre_walk_eval = save_thm
  ("mixed_event_types_pre_walk_eval",
   EVAL ``run_pipeline_stages ^mixed_event_types_rpolicy
           o1_pipeline_spec.ps_pre_walk_stages
           ^mixed_event_types_runtime_unit ^mixed_event_types_supply``)

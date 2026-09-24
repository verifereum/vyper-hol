(* Checked runtime-pipeline staging for the internal_tuple_call fixture. *)

Theory evalCompilerBytecodeAbiInternalTuplePipeline
Ancestors evalCompilerBytecodeAbiInternalTupleLowering compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Definition internal_tuple_call_runtime_pipeline_def:
  internal_tuple_call_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy prague_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

val internal_tuple_call_runtime_pipeline_step0 = SIMP_CONV pure_ss
  [internal_tuple_call_runtime_pipeline_def,
   optionTheory.option_case_def,
   evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_policy_eval,
   evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_lower_runtime_eval,
   LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  ``internal_tuple_call_runtime_pipeline
      task090_internal_tuple_call_program``
val internal_tuple_call_runtime_unit = optionSyntax.dest_some
  (rhs (concl
    evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_lower_runtime_eval))
val internal_tuple_call_rpolicy = optionSyntax.dest_some
  (rhs (concl
    evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_policy_eval))
val internal_tuple_call_run_pipeline_eval = save_thm
  ("internal_tuple_call_run_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
       ^internal_tuple_call_rpolicy o1_pipeline_spec
       ^internal_tuple_call_runtime_unit``)
val internal_tuple_call_runtime_pipeline_step1 = SIMP_CONV pure_ss
  [internal_tuple_call_run_pipeline_eval,
   optionTheory.OPTION_MAP_DEF,
   optionTheory.option_case_def,
   LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_runtime_pipeline_step0))
val internal_tuple_call_runtime_pipeline_eval = save_thm
  ("internal_tuple_call_runtime_pipeline_eval",
   TRANS internal_tuple_call_runtime_pipeline_step0
     internal_tuple_call_runtime_pipeline_step1)

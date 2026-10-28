(* Checked runtime-pipeline staging for the external-dynamic fixture. *)

Theory evalCompilerBytecodeAbiExternalDynamicPipeline
Ancestors evalCompilerSubsetAbiExternal compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val () = computeLib.upd_compset
  (computeLib.add_thms [contextTheory.compile_copy_memory_def])

Definition external_dynamic_runtime_pipeline_def:
  external_dynamic_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

Definition external_dynamic_runtime_compile_def:
  external_dynamic_runtime_compile tops =
    case external_dynamic_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

Definition external_dynamic_deploy_compile_def:
  external_dynamic_deploy_compile tops runtime =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_deploy_unit tops rpolicy runtime of
          NONE => NONE
        | SOME unit =>
            checked_unit_pipeline
              (λrp u. run_venom_pipeline (K T) (K T) (K T)
                 rp o1_pipeline_spec u)
              (K SOME) rpolicy unit
End

val external_dynamic_runtime_pipeline_eval =
  save_thm ("external_dynamic_runtime_pipeline_eval",
    EVAL ``external_dynamic_runtime_pipeline task090_external_dynamic_program``)

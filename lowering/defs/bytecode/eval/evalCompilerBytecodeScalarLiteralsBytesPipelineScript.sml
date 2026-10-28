(* Checked runtime-pipeline staging for the scalar_literals_bytes fixture. *)

Theory evalCompilerBytecodeScalarLiteralsBytesPipeline
Ancestors evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val () = computeLib.upd_compset
  (computeLib.add_thms [contextTheory.compile_copy_memory_def])

Definition scalar_literals_bytes_runtime_pipeline_def:
  scalar_literals_bytes_runtime_pipeline tops =
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

Definition scalar_literals_bytes_runtime_compile_def:
  scalar_literals_bytes_runtime_compile tops =
    case scalar_literals_bytes_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

Definition scalar_literals_bytes_deploy_compile_def:
  scalar_literals_bytes_deploy_compile tops runtime =
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

val scalar_literals_bytes_runtime_pipeline_eval =
  save_thm ("scalar_literals_bytes_runtime_pipeline_eval",
    EVAL ``scalar_literals_bytes_runtime_pipeline scalar_literals_bytes_program``)

(* Kernel-checked boundaries between a completed stack plan and byte encoding. *)
structure evalCompilerAssemblyLib = struct
open HolKernel Parse
open evalCompilerEntryLib evalCompilerBoundedLib

val assembly_resume_cs = entry_plan_readonly_cs
  [``:context_plan_acc``, ``:context_plan``, ``:spill_region``]
  |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
  |> computeLib.add_thms [optionTheory.option_case_lazily]
fun assembly_resume tm = let
  fun stop t = is_const t andalso List.exists
    (fn name => #Name (dest_thy_const t) = name)
    ["execute_plan", "assembly_target_safe", "assemble"]
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV assembly_resume_cs) tm end
val entry_assembly_open = entry_eval_stage assembly_resume "OPTION_MAP"
end

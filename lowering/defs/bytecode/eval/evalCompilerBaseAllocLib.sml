(* Normalize allocation inputs once, before the independent analyses. *)
structure evalCompilerBaseAllocLib = struct
open HolKernel Parse
open evalCompilerBaseLib

fun base_alloc_input i = let
  fun argument n cv = if n = 3 then RAND_CONV cv
    else RATOR_CONV (argument (n + 1) cv)
  val normalize = computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV
in base_eval_stage (argument i normalize) "concretize_function_fuel_in_context" end
end

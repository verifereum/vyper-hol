(* Normalize allocation inputs once, before the independent analyses. *)
structure evalCompilerBaseAllocLib = struct
open HolKernel Parse
open evalCompilerBaseLib

fun base_alloc_input i = let
  fun argument n cv = if n = 3 then RAND_CONV cv
    else RATOR_CONV (argument (n + 1) cv)
  val normalize = computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV
in base_eval_stage (argument i normalize) "concretize_function_fuel_in_context" end

(* The allocator now consumes imported allocation identities, rather than
   synthetic call frames. Expose its context-aware liveness analysis. *)
val base_alloc_liveness_open = base_eval_stage
  (SIMP_CONV pure_ss
    [concretizeMemLocDefsTheory.context_mem_livesets_def, boolTheory.LET_THM])
  "context_mem_livesets"
end

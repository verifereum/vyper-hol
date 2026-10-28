(* Downstream bytecode checks need completed plans, not internal worklists. *)
structure compilerScalarStageExportsLib = struct
  open HolKernel boolLib

  fun publish_plan () = let
    val context_head = prim_mk_const {Thy="stackPlanGen",Name="generate_context_plan"}
    val function_head = prim_mk_const {Thy="stackPlanGen",Name="generate_fn_plan"}
    fun head (_,equation) = fst(strip_comb(lhs(concl equation)))
    val roots = List.filter (fn entry =>
      same_const (head entry) context_head orelse same_const (head entry) function_head)
      (!evalCompilerBytecodeLib.pending_stage_values)
    val () = if List.exists (fn entry => same_const (head entry) context_head) roots then ()
      else raise Fail "completed runtime context certificate missing"
    val () = evalCompilerBytecodeLib.pending_stage_values := roots
    val () = evalCompilerBytecodeLib.publish_stage_values ()
    (* All plan theorems are already closed. Release private proof caches
       before the build saves its dependency context. *)
    val () = evalCompilerBytecodeLib.compiler_certificates := []
    val () = compilerInstructionPlannerEvalLib.normalization_certificates := []
    val () = compilerInstructionPlannerEvalLib.argument_certificates := []
  in () end
end

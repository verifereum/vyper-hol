(* Apply instruction cases directly when their checked premise fixes the target. *)
structure compilerModularPlannerEvalLib = struct
  open HolKernel boolLib

  val special_queries =
    [(prim_mk_const {Thy="stackPlanGen",Name="generate_phi_plan"},3),
     (prim_mk_const {Thy="stackPlanGen",Name="generate_offset_plan"},2)]

  fun configure () =
    (compilerBlockPlannerEvalLib.configure ();
     app (fn (head,arity) =>
       evalCompilerBytecodeLib.ensure_certificate_head head arity) special_queries)

  fun capture_heads head =
    if same_const head compilerPlannerEvalLib.inst_head then
      compilerBlockPlannerEvalLib.regular_head :: map fst special_queries
    else if List.exists (fn (query,_) => same_const head query) special_queries then []
    else compilerBlockPlannerEvalLib.capture_heads head

  fun instruction_case call = let
    val head = fst(strip_comb call)
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanInstructionCases" "generate_block_insts_plan_cons") call
    val instruction = hd(snd(strip_comb(rhs(concl unfolded))))
    val evidence = compilerInstructionPlannerEvalLib.checked_call instruction
    val result = rhs(concl evidence)
    val name = if optionSyntax.is_some result then "generate_block_insts_plan_some"
      else if optionSyntax.is_none result then "generate_block_insts_plan_none"
      else raise Fail "instruction result was not a concrete option"
    val inferred = evalCompilerBytecodeLib.timed_evaluation head "modular instruction inference"
      (fn () => MATCH_MP (SPEC_ALL(DB.fetch "stackPlanInstructionCases" name)) evidence)
    val selected = evalCompilerBytecodeLib.timed_evaluation head "modular instruction target"
      (fn () => if aconv (lhs(concl inferred)) call then inferred else PART_MATCH lhs inferred call)
  in if optionSyntax.is_none result then selected
    else compilerInstructionPlannerEvalLib.finish_case selected
  end

  fun warm_step goal =
    case !compilerPlannerEvalLib.pending of
      current::_ => if same_const (fst(strip_comb current)) compilerPlannerEvalLib.insts_head
          andalso listSyntax.is_cons (List.nth(snd(strip_comb current),9)) then let
        fun complete () = let
          val certificate = instruction_case current
          val () = if optionSyntax.is_some(rhs(concl certificate)) then ()
            else raise Fail "instruction suffix did not return SOME"
          val () = evalCompilerBytecodeLib.register_compile_eval certificate
          val () = evalCompilerBytecodeLib.pending_stage_values :=
            (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
          val () = compilerPlannerEvalLib.pending := tl(!compilerPlannerEvalLib.pending)
        in Tactical.ALL_TAC goal end
      in Lib.with_flag
          (evalCompilerBytecodeLib.planner_capture_heads,
           capture_heads(fst(strip_comb current))) complete ()
        handle compilerInstructionPlannerEvalLib.InputsPrepared => Tactical.ALL_TAC goal
          | evalCompilerBytecodeLib.PlannerBoundary child =>
              (compilerPlannerEvalLib.pending := child :: !compilerPlannerEvalLib.pending;
               Tactical.ALL_TAC goal)
      end else compilerPlannerEvalLib.warm_step_with capture_heads goal
    | [] => compilerPlannerEvalLib.warm_step_with capture_heads goal
end

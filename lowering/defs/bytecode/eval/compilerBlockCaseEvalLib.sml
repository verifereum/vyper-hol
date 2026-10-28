(* Compose the checked block-prefix pairs and the actual instruction plan. *)
structure compilerBlockCaseEvalLib = struct
  open HolKernel boolLib

  fun compute call = let
    val [liveness,dfg,cfg,func,bb,ps] = snd(strip_comb call)
    val entry_head = prim_mk_const {Thy="stackPlanBlockCases",Name="planner_block_entry"}
    val cleanup_head = prim_mk_const {Thy="stackPlanBlockCases",Name="planner_block_cleanup"}
    val entry = compilerInstructionPlannerEvalLib.checked_call
      (boolSyntax.list_mk_icomb(entry_head,[liveness,func,bb,ps]))
    val (_,ps1) = pairSyntax.dest_pair(rhs(concl entry))
    val cleanup = compilerInstructionPlannerEvalLib.checked_call
      (boolSyntax.list_mk_icomb(cleanup_head,[liveness,cfg,func,bb,ps1]))
    val selected = evalCompilerBytecodeLib.timed_evaluation
      (fst(strip_comb call)) "block prefix case" (fn () =>
        PART_MATCH lhs (MATCH_MP
          (SPEC_ALL(DB.fetch "stackPlanBlockCases" "generate_block_plan_parts"))
          (CONJ entry cleanup)) call)
  in compilerInstructionPlannerEvalLib.finish_case selected end
end

(* Compose the checked branch and successor-tail results. *)
structure compilerTraversalCaseEvalLib = struct
  open HolKernel boolLib

  fun select_case name evidence call =
    PART_MATCH lhs (MATCH_MP
      (SPEC_ALL(DB.fetch "stackPlanTraversalCases" name)) evidence) call

  fun compute_function call = let
    val [liveness,dfg,cfg,func,work,visited,ps] = snd(strip_comb call)
    val (label,_) = listSyntax.dest_cons work
    val seen = evalCompilerBytecodeLib.timed_evaluation (fst(strip_comb call))
      "function visited" (fn () => computeLib.EVAL_CONV ``MEM ^label ^visited``)
  in if aconv (rhs(concl seen)) T then
      select_case "generate_fn_plan_aux_singleton_visited" (EQT_ELIM seen) call
    else let
      val lookup_head = prim_mk_const {Thy="venomInst",Name="lookup_block"}
      val found = compilerInstructionPlannerEvalLib.checked_call
        (boolSyntax.list_mk_icomb(lookup_head,[label,``(^func).fn_blocks``]))
    in if optionSyntax.is_none(rhs(concl found)) then
        select_case "generate_fn_plan_aux_singleton_missing"
          (CONJ (EQF_ELIM seen) found) call
      else let
        val bb = optionSyntax.dest_some(rhs(concl found))
        val block = compilerInstructionPlannerEvalLib.checked_call
          (boolSyntax.list_mk_icomb(evalCompilerBytecodeLib.planner_block_head,
            [liveness,dfg,cfg,func,bb,ps]))
        val result = rhs(concl block)
        val name = if optionSyntax.is_some result then "generate_fn_plan_aux_singleton_some"
          else if optionSyntax.is_none result then "generate_fn_plan_aux_singleton_none"
          else raise Fail "block result was not a concrete option"
        val selected = select_case name
          (CONJ (EQF_ELIM seen) (CONJ found block)) call
      in if optionSyntax.is_none result then selected
        else compilerInstructionPlannerEvalLib.finish_case selected
      end
    end
  end

  fun compute call = let
    val [liveness,dfg,cfg,func,saved_stack,saved_spilled,succs,visited,ps] =
      snd(strip_comb call)
    val (succ,_) = listSyntax.dest_cons succs
    val branch_ps = ``^ps with <|ps_stack := ^saved_stack; ps_spilled := ^saved_spilled|>``
    val branch_head = prim_mk_const {Thy="stackPlanGen",Name="generate_fn_plan_aux"}
    val branch = compilerInstructionPlannerEvalLib.checked_call
      (boolSyntax.list_mk_icomb(branch_head,
        [liveness,dfg,cfg,func,listSyntax.mk_list([succ],type_of succ),visited,branch_ps]))
    val result = rhs(concl branch)
    val name = if optionSyntax.is_some result then "generate_succs_plan_some"
      else if optionSyntax.is_none result then "generate_succs_plan_none"
      else raise Fail "branch result was not a concrete option"
    val selected = evalCompilerBytecodeLib.timed_evaluation
      (fst(strip_comb call)) "successor branch case" (fn () =>
        PART_MATCH lhs (MATCH_MP
          (SPEC_ALL(DB.fetch "stackPlanTraversalCases" name)) branch) call)
  in if optionSyntax.is_none result then selected
    else compilerInstructionPlannerEvalLib.finish_case selected
  end
end

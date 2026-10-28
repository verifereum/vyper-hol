(* Stage the existing cleanup cases and their observed input lists. *)
structure compilerPlanCleanupEvalLib = struct
  open HolKernel boolLib
  fun rule name = DB.fetch "stackPlanCleanupCases" name

  fun clean_result checked metadata current = let
    val [liveness,cfg,func,bb,ps] = snd (strip_comb current)
    val predecessors = metadata ``cfg_preds_of ^cfg (^bb).bb_label``
    val (labels,_) = listSyntax.dest_list (rhs (concl predecessors))
  in case labels of
    [] => compilerCleanupEvalLib.apply_case
      (rule "planner_cleanup_no_predecessors") current predecessors
  | _::_::_ => compilerCleanupEvalLib.apply_case
      (rule "planner_cleanup_many_predecessors") current predecessors
  | [_] => let
      val selected = compilerCleanupEvalLib.apply_case
        (rule "planner_cleanup_single_predecessor") current predecessors
      val result = checked (rhs (concl selected))
    in TRANS selected result end
  end

  fun single_result checked metadata current = let
    val [liveness,cfg,func,bb,ps,predecessor] = snd (strip_comb current)
    val successors = metadata ``LENGTH (cfg_succs_of ^cfg ^predecessor) <= 1``
  in if aconv (rhs (concl successors)) T then
      compilerCleanupEvalLib.apply_case (rule "planner_cleanup_single_skip")
        current (EQT_ELIM successors)
    else let
      val found = metadata ``lookup_block ^predecessor (^func).fn_blocks``
    in if optionSyntax.is_none (rhs (concl found)) then
        compilerCleanupEvalLib.apply_case (rule "planner_cleanup_single_missing")
          current found
      else let
        val selected = compilerCleanupEvalLib.apply_case
          (rule "planner_cleanup_single_found") current
          (CONJ (EQF_ELIM successors) found)
        val call = rhs (concl selected)
        val safety_call = List.nth (snd (strip_comb call),3)
        val safety = checked safety_call
        val prepared = compilerSingleUseEvalLib.argument 4 (fn _ => safety) call
        val result = checked (rhs (concl prepared))
      in TRANS selected (TRANS prepared result) end
    end
  end
end

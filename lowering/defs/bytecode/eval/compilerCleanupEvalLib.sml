(* Select the actual cleanup case before instantiating its continuation. *)
structure compilerCleanupEvalLib = struct
  open HolKernel boolLib bossLib stackPlanCleanupCasesTheory

  fun apply_case rule target evidence =
    evalCompilerBytecodeLib.timed_evaluation (fst(strip_comb target)) "cleanup case"
      (fn () => PART_MATCH lhs (MATCH_MP (SPEC_ALL rule) evidence) target)

  fun compute_safety call = let
    val [cfg,func,bb] = snd(strip_comb call)
    val bound = evalCompilerBytecodeLib.timed_evaluation (fst(strip_comb call))
      "cleanup frame upper bound" (fn () => computeLib.EVAL_CONV
        ``LENGTH (planner_cleanup_candidates ^func) + cleanup_max_transient ^func <= 1024``)
  in if aconv (rhs(concl bound)) T then let
      val reduced = apply_case planner_cleanup_safety_frame_bound call (EQT_ELIM bound)
      val result = computeLib.EVAL_CONV(rhs(concl reduced))
    in TRANS reduced result end
    else computeLib.EVAL_CONV call
  end

  fun compute call = let
    val (_,args) = strip_comb call
    val [liveness,cfg,func,bb,ps] = args
    val preds_eq = evalCompilerBytecodeLib.timed_evaluation (fst(strip_comb call))
      "cleanup predecessors" (fn () =>
        computeLib.EVAL_CONV ``cfg_preds_of ^cfg (^bb).bb_label``)
    val (preds,_) = listSyntax.dest_list(rhs(concl preds_eq))
  in case preds of
    [] => apply_case planner_cleanup_no_predecessors call preds_eq
  | _::_::_ => apply_case planner_cleanup_many_predecessors call preds_eq
  | [pred] => let
      val selected = apply_case planner_cleanup_single_predecessor call preds_eq
      val single = rhs(concl selected)
      val succ_eq = evalCompilerBytecodeLib.timed_evaluation (fst(strip_comb single))
        "cleanup successor count" (fn () =>
          computeLib.EVAL_CONV ``LENGTH (cfg_succs_of ^cfg ^pred) <= 1``)
      val next = if aconv (rhs(concl succ_eq)) T then
          apply_case planner_cleanup_single_skip single (EQT_ELIM succ_eq)
        else let
          val found = evalCompilerBytecodeLib.timed_evaluation (fst(strip_comb single))
            "cleanup lookup" (fn () =>
              computeLib.EVAL_CONV ``lookup_block ^pred (^func).fn_blocks``)
        in if optionSyntax.is_none(rhs(concl found)) then
            apply_case planner_cleanup_single_missing single found
          else let
            val boundary = apply_case planner_cleanup_single_found single
              (CONJ (EQF_ELIM succ_eq) found)
            val (evaluated,_) = evalCompilerBytecodeLib.evaluate_call(rhs(concl boundary))
          in TRANS boundary evaluated end
        end
    in TRANS selected next end
  end
end

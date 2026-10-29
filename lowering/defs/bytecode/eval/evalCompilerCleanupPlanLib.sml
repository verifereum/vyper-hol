(* Kernel-checked cleanup-aware planner evaluation. Preserve the context's
   actual cleanup heights, growth table, spill base and label counter;
   already concrete context results need no planner-call extraction. *)
structure evalCompilerCleanupPlanLib = struct
open HolKernel Parse boolLib bossLib

fun cleanup_plan_conv tm =
  case total (find_term (fn t =>
      can (match_term ``generate_fn_plan_with_cleanup ch growth f spill labels``) t
      orelse can (match_term
        ``generate_fn_plan_with_cleanup_analyzed live dfg cfg ch growth f spill labels``) t)) tm of
    NONE => REFL tm
  | SOME call => let
      val (head, args) = strip_comb call
      val analyzed = same_const head ``generate_fn_plan_with_cleanup_analyzed``
      val func = List.nth (args, if analyzed then 5 else 2)
      val unfolded = if analyzed then REFL call else
        REWR_CONV stackPlanGenTheory.generate_fn_plan_with_cleanup_def call
      val cached = PURE_REWRITE_CONV
        [EVAL ``liveness_analyze ^func``, EVAL ``dfg_build_function ^func``,
         EVAL ``cfg_analyze ^func``] (rhs (concl unfolded))
      val reduced = (REWR_CONV
        stackPlanGenTheory.generate_fn_plan_with_cleanup_analyzed_def THENC EVAL)
        (rhs (concl cached))
      val plan = TRANS unfolded (TRANS cached reduced)
      val () = computeLib.upd_compset (computeLib.add_thms [plan])
      val rewritten = PURE_REWRITE_CONV [plan] tm
      val evaluated = EVAL (rhs (concl rewritten))
    in TRANS rewritten (TRANS evaluated
      (cleanup_plan_conv (rhs (concl evaluated)))) end
end

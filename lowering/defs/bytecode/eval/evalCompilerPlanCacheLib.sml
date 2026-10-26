(* Kernel-proved shared planner summaries and isolated cleanup guards. *)
structure evalCompilerPlanCacheLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerEntryLib

val entry_plan_summary_thms = ref ([] : thm list)
fun entry_plan_cache_call name args = let
  val call = list_mk_comb
    (prim_mk_const {Thy="stackPlanGen",Name=name},args)
  val () = if List.null (free_vars call) then ()
    else raise Fail "planner summary cache requires a closed call"
  val th = computeLib.EVAL_CONV call
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val () = if List.null (hyp th) andalso List.null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail "planner summary cache is not kernel closed"
in evalCompilerBytecodeLib.add_compile_eval th;
   computeLib.upd_compset (computeLib.add_thms [th]);
   entry_plan_summary_thms := th :: !entry_plan_summary_thms
end
fun entry_plan_cache name indices g = let
  fun selected tm = let val (h,args) = strip_comb tm in
    entry_is_analyzed h andalso
    List.length args = entry_function_arity (type_of h) end
  val (head,args) = strip_comb (find_term selected (lhs (snd g)))
  val () = entry_plan_cache_call name
    (List.map (fn i => List.nth (args,entry_plan_argument_index head i)) indices)
in ALL_TAC g end
fun plan_cache_vars g =
  (entry_plan_summary_thms := []; entry_plan_cache "cleanup_frame_vars" [3] g)
val plan_cache_transient = entry_plan_cache "cleanup_max_transient" [3]
val plan_cache_halting = entry_plan_cache "must_halt_labels" [2,3]

(* Rewrite the three summaries explicitly before computing the small guard.
   This also diagnoses cache mismatches without recomputing a whole-function
   nub inside a block-cleanup tactic. *)
fun entry_cached_cleanup evaluate tm =
  case List.find (fn th => aconv (lhs (concl th)) tm) (!entry_plan_summary_thms) of
    SOME th => th
  | NONE => let
      val opened = PURE_REWRITE_CONV
        [stackPlanGenTheory.cleanup_elision_safe_def,
         stackPlanGenTheory.cleanup_height_safe_def] tm
      val rewritten = (PURE_REWRITE_CONV (!entry_plan_summary_thms)
        (rhs (concl opened)) handle UNCHANGED => REFL (rhs (concl opened)))
      val body = rhs (concl rewritten)
      val pending = List.filter (fn name => entry_has_call [name] body)
        ["cleanup_frame_vars", "cleanup_max_transient", "must_halt_labels"]
      val () = if List.null pending then () else
        raise Fail ("cleanup summary mismatch: " ^ String.concatWith ", " pending)
      val evaluated = evaluate body
      val answer = rhs (concl evaluated)
      val () = if aconv answer boolSyntax.T orelse aconv answer boolSyntax.F then ()
        else raise Fail "incomplete block-cleanup guard"
      val th = TRANS opened (TRANS rewritten evaluated)
      val () = entry_plan_summary_thms := th :: !entry_plan_summary_thms
    in th end
end

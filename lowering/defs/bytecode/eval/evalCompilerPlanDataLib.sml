(* Keep immutable planner records out of repeated goal contexts. Computation
   expands their local abbreviation assumptions only inside the selected call;
   final un-abbreviation removes every assumption from the parity theorem. *)
structure evalCompilerPlanDataLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerEntryLib

val entry_plan_abbrev_defs = ref ([] : thm list)
fun entry_plan_closed tm = List.all (fn v =>
  List.exists (fn th => aconv v (lhs (concl th))) (!entry_plan_abbrev_defs))
  (free_vars tm)
fun entry_plan_has_call names tm = can (find_term (fn t => let
  val (h,args) = strip_comb t
in is_const h andalso List.exists (fn n => #Name (dest_thy_const h) = n) names
   andalso List.length args = entry_function_arity (type_of h)
   andalso entry_plan_closed t end)) tm

fun entry_plan_compute evaluate tm = if List.null (free_vars tm) then evaluate tm
  else let
    fun replace reverse t =
      case List.find (fn th => aconv t
        (if reverse then rhs (concl th) else lhs (concl th))) (!entry_plan_abbrev_defs) of
        SOME th => if reverse then SYM th else th
      | NONE => NO_CONV t
    val expanded = (ONCE_DEPTH_CONV (replace false) tm
      handle UNCHANGED => REFL tm)
    val closed = rhs (concl expanded)
    val () = if List.null (free_vars closed) then ()
      else raise Fail "planner computation has unresolved variables"
    val evaluated = evaluate closed
    val compacted = (ONCE_DEPTH_CONV (replace true) (rhs (concl evaluated))
      handle UNCHANGED => REFL (rhs (concl evaluated)))
  in TRANS expanded (TRANS evaluated compacted) end

fun entry_plan_abbrev name index g = let
  fun selected tm = let val (h,args) = strip_comb tm in
    is_const h andalso #Name (dest_thy_const h) = "generate_fn_plan_analyzed"
    andalso List.length args = 6 andalso entry_plan_closed tm end
  val args = snd (strip_comb (find_term selected (lhs (snd g))))
  val value = List.nth(args,index)
  val variable = mk_var (name,type_of value)
  val () = if List.exists (aconv variable) (free_varsl (snd g :: fst g)) then
      raise Fail ("planner abbreviation already exists: " ^ name) else ()
  fun remember next = let
    fun matching a = let
      val eq = rand a
    in #Name (dest_thy_const (rator a)) = "Abbrev" andalso
       aconv (lhs eq) variable end handle HOL_ERR _ => false
    val assumption = valOf (List.find matching (fst next))
    val th = REWRITE_RULE [markerTheory.Abbrev_def] (ASSUME assumption)
    val () = entry_plan_abbrev_defs := th :: !entry_plan_abbrev_defs
  in ALL_TAC next end
in (markerLib.ABBREV_TAC (mk_eq(variable,value)) >> remember) g end

fun entry_plan_unabbrev name g =
  (markerLib.UNABBREV_TAC name >> (fn next =>
    (entry_plan_abbrev_defs := List.filter (fn th =>
       fst (dest_var (lhs (concl th))) <> name) (!entry_plan_abbrev_defs);
     ALL_TAC next))) g
end

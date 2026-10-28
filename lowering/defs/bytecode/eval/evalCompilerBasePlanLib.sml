(* Checked, bounded construction of the main function's shared variable set. *)
structure evalCompilerBasePlanLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

fun base_plan_analyzed tm = let
  val (head,args) = strip_comb tm
in entry_is_analyzed head andalso
   length args = entry_function_arity (type_of head) andalso
   List.null (free_vars tm)
end

(* Compact one DFG map per boundary, independently of planner arity. *)
fun base_plan_compact_dfg_map map_type = CONV_TAC (LAND_CONV
  (base_first_conv base_plan_analyzed (fn tm => let
    val (_,args) = strip_comb tm
    fun argument i n convert =
      if i = n - 1 then RAND_CONV convert
      else RATOR_CONV (argument i (n - 1) convert)
    val compact = base_first_conv
      (fn t => finite_mapSyntax.is_fupdate t andalso type_of t = map_type)
      entry_compact_maps
  in argument 1 (length args) compact tm end)))

val base_plan_vars_equation = ref (NONE : thm option)
fun base_plan_vars_open g = let
  val target = find_term base_plan_analyzed (lhs (snd g))
  val (head,args) = strip_comb target
  val func = List.nth (args,entry_plan_argument_index head 3)
  val call = mk_comb (``stackPlanGen$cleanup_frame_vars``,func)
  val th = REWR_CONV stackPlanGenTheory.cleanup_frame_vars_def call
in base_plan_vars_equation := SOME th; ALL_TAC g end
fun base_plan_vars_update convert g = let
  val th = valOf (!base_plan_vars_equation)
  val next = TRANS th (Conv.QCONV convert (rhs (concl th)))
in base_plan_vars_equation := SOME next; ALL_TAC g end
val base_plan_vars_input = base_plan_vars_update
  (RAND_CONV computeLib.EVAL_CONV)

(* Unfold precisely this many original list clauses; each MEM computation
   is closed and no recursive nub call is evaluated by the native evaluator. *)
fun base_nub_prefix 0 tm = REFL tm
  | base_nub_prefix n tm =
    if flow_call "nub" tm then
      if listSyntax.is_nil (rand tm) then REWR_CONV (cj 1 listTheory.nub_def) tm
      else let
        val opened = REWR_CONV (cj 2 listTheory.nub_def) tm
        val condition = RATOR_CONV (RATOR_CONV
          (RAND_CONV computeLib.EVAL_CONV)) (rhs (concl opened))
        val selected = FIRST_CONV (List.map REWR_CONV
          (Drule.BODY_CONJUNCTS COND_CLAUSES)) (rhs (concl condition))
        val th = TRANS opened (TRANS condition selected)
      in TRANS th (base_nub_prefix (n - 1) (rhs (concl th))) end
    else if can listSyntax.dest_cons tm then RAND_CONV (base_nub_prefix n) tm
    else REFL tm
val base_plan_vars_tick = base_plan_vars_update (base_nub_prefix 16)
fun base_plan_vars_finish g = let
  val th = valOf (!base_plan_vars_equation)
  val () = if entry_has_call ["nub"] (rhs (concl th)) then
      raise Fail "planner variable summary has pending nub calls" else ()
  val () = if can listSyntax.dest_list (rhs (concl th)) then ()
    else raise Fail "planner variable summary is not a literal list"
  val () = evalCompilerBytecodeLib.add_compile_eval th
  val () = computeLib.upd_compset (computeLib.add_thms [th])
  val () = base_plan_vars_equation := NONE
in plan_cache_vars g end
end

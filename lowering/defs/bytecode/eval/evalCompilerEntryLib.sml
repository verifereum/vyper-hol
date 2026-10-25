(* Checked evaluation boundaries shared by the external-entry parity fixtures. *)
structure evalCompilerEntryLib = struct
open HolKernel Parse boolLib bossLib
open boolTheory listTheory compileVyperTheory concretizeMemLocDefsTheory
     alistTheory byteTheory integer_wordTheory optionTheory finite_mapLib

(* Compiler arithmetic includes word widths as well as integer operations.
   Install these before any private evaluator copies the shared compset. *)
val () = computeLib.upd_compset (wordsLib.add_words_compset false)
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset (fn cs => cs
  |> (fn cs' => computeLib.scrub_const cs'
       (prim_mk_const {Thy="contractABI",Name="function_selector"}))
  |> computeLib.add_conv
       (prim_mk_const {Thy="contractABI",Name="function_selector"},2,
        cv_transLib.cv_eval)
  (* Recompile these rules against the new selector entry. Existing compiled
     RHS closures retain references to their original compset entries. *)
  |> computeLib.add_thms [compute_selector_def, build_compile_env_def])
(* Evaluate the public structural equations rather than the mutual-recursion
   implementation relations hidden behind these interfaces. *)
val () = computeLib.upd_compset (fn cs => cs
  |> (fn cs' => computeLib.scrub_const cs' ``compile_expr``)
  |> (fn cs' => computeLib.scrub_const cs' ``compile_stmt``)
  |> (fn cs' => computeLib.scrub_const cs' ``compile_stmts``)
  |> computeLib.add_thms [exprLoweringTheory.compile_expr_component_eq,
                         stmtLoweringTheory.compile_stmt_def])

(* Each selected conversion is a separate timed proof step. This avoids
   evaluating both compiler units in one opaque EVAL_TAC invocation. *)
fun entry_function_arity ty =
  case total dom_rng ty of NONE => 0
  | SOME (_,range) => 1 + entry_function_arity range

fun entry_eval_stage_names evaluate names = CONV_TAC (LAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV (fn tm =>
  let val (h,args) = strip_comb tm
  in if is_const h andalso
        List.exists (fn name => #Name (dest_thy_const h) = name) names andalso
        List.length args >= entry_function_arity (type_of h) andalso
        List.null (free_vars tm)
     then let
       val () = case !computeLib.stoppers of NONE => ()
         | SOME _ => raise Fail "unexpected stopper outside entry_chunk"
       val th = CHANGED_CONV evaluate tm
       in th end
     else NO_CONV tm
   end))))

fun entry_eval_stage evaluate name = entry_eval_stage_names evaluate [name]

val entry_stage = entry_eval_stage
  (fn tm => computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm)
val entry_strict_stage = entry_eval_stage computeLib.EVAL_CONV

(* Fixed-point analyses retain shadowed map updates. Normalize each complete
   map once before it is duplicated through planner continuations. *)
fun entry_compact_maps tm =
  if finite_mapSyntax.is_fupdate tm then
    finite_mapLib.fupdate_NORMALISE_CONV tm
  else SUB_CONV entry_compact_maps tm

val entry_analysis_stage = entry_eval_stage (fn tm => let
  val th = computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm
in TRANS th (entry_compact_maps (rhs (concl th))) end)

val entry_guard = entry_eval_stage (fn tm => let
  val th = computeLib.EVAL_CONV tm
  val result = rhs (concl th)
in if aconv result boolSyntax.T orelse aconv result boolSyntax.F then th
   else raise Fail ("incomplete closed Boolean computation: " ^
     term_to_string (fst (strip_comb tm)))
end)

(* Native bounded CBV, retaining inactive abstractions. Every invocation is
   independently timed by holbuild and returns an ordinary kernel equality. *)
fun entry_chunk budget = CONV_TAC (LAND_CONV (fn tm => let
  val remaining = ref budget
  val previous = case !computeLib.stoppers of NONE => (fn _ => false)
    | SOME f => f
  fun stop t = if !remaining <= 0 then true
    else (remaining := !remaining - 1; previous t)
in
  Lib.with_flag (computeLib.stoppers,SOME stop)
    (computeLib.WEAK_CBV_CONV (computeLib.the_compset())) tm
end))

val entry_admin_rules =
  [LET_THM, optionTheory.option_case_def, pairTheory.pair_case_thm,
    pairTheory.UNCURRY_DEF,
    NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, COND_CLAUSES,
    boolTheory.REFL_CLAUSE,
    combinTheory.K_THM, listTheory.APPEND] @
   List.concat (List.map (fn ty => #rewrs (TypeBase.simpls_of ty))
     [``:compilation_unit``, ``:venom_context``, ``:ir_function``,
       ``:ir_supply``, ``:fn_pass_output``, ``:pipeline_output``])
val entry_admin =
  simp_tac pure_ss entry_admin_rules >> BETA_TAC >>
  simp_tac pure_ss entry_admin_rules

val entry_pass_begin =
  simp_tac pure_ss [Once venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  entry_stage "unit_with_current_fn" >> entry_admin

val entry_pass_emit = entry_pass_begin >>
  entry_stage "execute_configured_fn_pass" >> entry_admin

val entry_pass_check =
  entry_guard "fn_pass_effects_hold" >>
  entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >>
  entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin

val entry_begin_mapped_stage =
  simp_tac pure_ss [Once venomPipelineRunnerTheory.run_pipeline_stages_def] >>
  simp_tac pure_ss [venomPipelineRunnerTheory.run_pipeline_stage_def,
    venomPipelineRunnerTheory.run_mapped_functions_def] >>
  entry_stage "ctx_fn_names" >>
  simp_tac pure_ss [venomPipelineRunnerTheory.run_named_fn_schedules_def,
    venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  entry_guard "ir_supply_covers_unit" >>
  entry_stage "lookup_unique_function" >> entry_admin

val entry_install_function =
  entry_stage "run_configured_fn_pass_fold" >> entry_admin >>
  entry_stage "replace_unique_function" >> entry_admin >>
  entry_stage "apply_unit_label_map" >> entry_admin >>
  entry_guard "unit_labels_wf" >> entry_guard "list_subset" >>
  entry_guard "ir_supply_covers_unit" >>
  entry_guard "unit_global_inst_ids_distinct" >> entry_admin

val () = computeLib.upd_compset (computeLib.add_thms
  [makeSsaCurrentDefsTheory.make_ssa_current_fn_def])


val entry_plan_admin_rules = entry_admin_rules @
    List.concat (List.map (fn ty => #rewrs (TypeBase.simpls_of ty))
      [``:context_plan_acc``, ``:context_plan``, ``:plan_state``, ``:spill_alloc``])
val entry_plan_admin =
  simp_tac pure_ss entry_plan_admin_rules >> BETA_TAC >>
  simp_tac pure_ss entry_plan_admin_rules

(* Reduce the active case spine without traversing deferred continuations.
   Planner recursion carries large analysis records through those branches. *)
val entry_plan_spine_rules = List.concat (List.map Drule.BODY_CONJUNCTS
  [optionTheory.option_case_def, pairTheory.pair_case_thm,
   pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND,
   LET_THM, COND_CLAUSES, optionTheory.OPTION_MAP_DEF])
val entry_plan_root_conv = FIRST_CONV
  (BETA_CONV :: List.map REWR_CONV entry_plan_spine_rules)

fun entry_plan_spine_conv tm = let
  fun argument i n cv =
    if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  val root = total (CHANGED_CONV entry_plan_root_conv) tm
in case root of
    SOME th => TRANS th (entry_plan_spine_conv (rhs (concl th)))
  | NONE => let
      val (h,args) = strip_comb tm
      val name = if is_const h then #Name (dest_thy_const h) else ""
      val active = case (name,List.length args) of
          ("option_CASE",3) => SOME 0
        | ("pair_CASE",2) => SOME 0
        | ("UNCURRY",2) => SOME 1
        | ("OPTION_MAP",2) => SOME 1
        | ("COND",3) => SOME 0
        | _ => NONE
    in case active of
        NONE =>
          if is_abs h andalso is_comb tm then let
            val th = RATOR_CONV entry_plan_spine_conv tm
          in if aconv (lhs (concl th)) (rhs (concl th)) then th
             else TRANS th (entry_plan_spine_conv (rhs (concl th)))
          end else REFL tm
      | SOME i => let
          val th = argument i (List.length args) entry_plan_spine_conv tm
        in if aconv (lhs (concl th)) (rhs (concl th)) then th
           else TRANS th (entry_plan_spine_conv (rhs (concl th)))
        end
    end
end
val entry_plan_spine_admin = CONV_TAC (LAND_CONV entry_plan_spine_conv)

(* Resume the real planner only as far as its next complete block request.
   Each block evaluation remains a separate timed, kernel-checked conversion. *)
fun entry_plan_resume tm = let
  val cs = computeLib.set_skip (computeLib.copy (computeLib.the_compset()))
    boolSyntax.conditional (SOME 1)
    |> computeLib.add_thms [optionTheory.option_case_lazily,
         stackPlanGenTheory.generate_fn_plan_analyzed_def,
         stackPlanGenTheory.generate_fn_plan_aux_def]
  val resume = Lib.with_flag (computeLib.stoppers,
    SOME (fn t => is_const t andalso
      #Name (dest_thy_const t) = "generate_block_plan"))
    (computeLib.WEAK_CBV_CONV cs)
  val th = FIRST_CONV
    [REWR_CONV (cj 1 stackPlanGenTheory.generate_fn_plan_aux_def),
     REWR_CONV (cj 3 stackPlanGenTheory.generate_fn_plan_aux_def), resume] tm
in th
end
val entry_plan_once = entry_eval_stage_names entry_plan_resume
  ["generate_fn_plan_analyzed", "generate_fn_plan_aux", "generate_succs_plan"]

fun entry_has_call names tm = can (find_term (fn t =>
  let val (h,args) = strip_comb t
  in is_const h andalso
     List.exists (fn name => #Name (dest_thy_const h) = name) names andalso
     List.length args >= entry_function_arity (type_of h) andalso
     List.null (free_vars t)
  end)) tm
fun entry_has_block tm = entry_has_call ["generate_block_plan"] tm

fun entry_plan_control g =
  if entry_has_block (lhs (snd g)) then ALL_TAC g
  else (entry_plan_once >> entry_plan_spine_admin >> entry_plan_control) g

fun entry_plan_finish g =
  if entry_has_block (lhs (snd g)) then
    raise Fail "planner still has an unevaluated block"
  else if entry_has_call
    ["generate_fn_plan_analyzed", "generate_fn_plan_aux", "generate_succs_plan"]
    (lhs (snd g)) then
      (entry_plan_once >> entry_plan_spine_admin >> entry_plan_finish) g
  else ALL_TAC g

val entry_plan_block = entry_eval_stage (fn tm => let
  val th = computeLib.EVAL_CONV tm
in if optionSyntax.is_some (rhs (concl th)) then th
   else raise Fail "block planning did not produce a complete successful result"
end) "generate_block_plan"

(* A bounded fixture may finish before all of its explicit planner boundaries.
   Skip only when the planner has no remaining closed work. Final byte equality
   still requires successful code generation and the exact pinned result. *)
fun entry_plan_next_control g =
  if entry_has_block (lhs (snd g)) then ALL_TAC g
  else if entry_has_call
    ["generate_fn_plan_analyzed", "generate_fn_plan_aux", "generate_succs_plan"]
    (lhs (snd g)) then
      (entry_plan_once >> entry_plan_spine_admin >> entry_plan_next_control) g
  else ALL_TAC g
fun entry_plan_next_block g =
  if entry_has_block (lhs (snd g)) then entry_plan_block g else ALL_TAC g

fun entry_report_result g = let
  val (actual,expected) = dest_eq (snd g)
  fun byte_value tm = Arbnum.toInt (Arbnum.mod
    (wordsSyntax.dest_word_literal tm, Arbnum.fromInt 256))
  fun first_difference i (a::xs) (b::ys) =
        if byte_value a = byte_value b then first_difference (i+1) xs ys else SOME i
    | first_difference _ [] [] = NONE
    | first_difference i _ _ = SOME i
  fun report label actual expected = let
    val xs = #1 (listSyntax.dest_list actual)
    val ys = #1 (listSyntax.dest_list expected)
    fun window i zs = String.concatWith " "
      (List.map (Int.toString o byte_value)
        (List.take (List.drop (zs,Int.min (List.length zs,Int.max (0,i-5))),
          Int.min (15,List.length zs - Int.min (List.length zs,Int.max (0,i-5))))))
    val status = case first_difference 0 xs ys of
        NONE => "match"
      | SOME i => "first difference " ^ Int.toString i ^
          " actual=" ^ window i xs ^ " expected=" ^ window i ys
  in print (label ^ " actual=" ^ Int.toString (List.length xs) ^
       " expected=" ^ Int.toString (List.length ys) ^ " " ^ status ^ "\n") end
  val () = if optionSyntax.is_some actual andalso optionSyntax.is_some expected then let
      val (ad,ar) = pairSyntax.dest_pair (optionSyntax.dest_some actual)
      val (ed,er) = pairSyntax.dest_pair (optionSyntax.dest_some expected)
    in report "deploy" ad ed; report "runtime" ar er end
    else print ("computed compiler result: " ^ term_to_string actual ^ "\n")
in ALL_TAC g end

end

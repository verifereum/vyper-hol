(* Bounded pass, scheduling, and readiness evaluation. *)
structure foldedValueParityAbiDftLib :> foldedValueParityAbiDftLib = struct
open HolKernel Parse boolLib bossLib boolTheory numLib
open foldedValueParityLib foldedValueParityAbiComputeTheory

val () = foldedValueParityLib.setup ();
val () = computeLib.upd_compset (fn cs => cs
  |> (fn cs' => computeLib.scrub_const cs' ``reduce_depth_plan``)
  |> (fn cs' => computeLib.scrub_const cs' ``generate_block_insts_plan``)
  |> computeLib.add_thms
    [stackPlanGenComputeTheory.reduce_depth_plan_compute,
     stackPlanGenComputeTheory.generate_block_insts_plan_compute]);
val () = foldedValueParityLib.refresh_compset ();
val parity_compset = computeLib.copy (computeLib.the_compset ());

(* Relink compiled RHS references before installing private evaluation flags.
   Preserve both rewrite priority and native conversion order. *)
fun relink_rules include_equality roots original = let
  val table = computeLib.listItems original
  fun key term = let val {Name, Thy, ...} = dest_thy_const term in (Name, Thy) end
  fun rules_of transforms = List.concat
    (map (fn clauses.RRules thms => thms | _ => []) transforms)
  fun visit [] seen = seen
    | visit (name::pending) seen =
        if List.exists (fn old => old = name) seen then visit pending seen else let
          val transforms = case List.find (fn (candidate, _) => candidate = name) table of
            NONE => [] | SOME (_, actions) => actions
          val dependencies = List.concat (map
            (fn th => map key (find_terms is_const (concl th))) (rules_of transforms))
        in visit (dependencies @ pending) (name::seen) end
  val reachable = visit (map key roots) []
  val equality_key = key boolSyntax.equality
  fun rewrite_only (_, transforms) = not (null transforms) andalso
    List.all (fn clauses.RRules _ => true | _ => false) transforms
  val entries = List.filter (fn entry as (name, _) =>
    (rewrite_only entry orelse (include_equality andalso name = equality_key)) andalso
    List.exists (fn needed => needed = name) reachable) table
  val cleared = List.foldl (fn (((name, thy), _), cs) =>
    computeLib.scrub_const cs (prim_mk_const {Name = name, Thy = thy}))
    (computeLib.copy original) entries
  fun reflexive_equality tm = let val (left, right) = dest_eq tm in
    if aconv left right then EQT_INTRO (REFL left) else raise Conv.UNCHANGED
  end
  val with_reflexivity = computeLib.add_conv
    (boolSyntax.equality, 2, reflexive_equality) cleared
  fun replay (clauses.RRules thms, cs) = computeLib.add_thms (rev thms) cs
    | replay (clauses.Conversion conversion, cs) = computeLib.add_conv
        (boolSyntax.equality, 2, conversion) cs
in List.foldl (fn ((_, actions), cs) => List.foldl replay cs actions)
     with_reflexivity entries end;
fun planner_beta_conv tm = Thm.Beta (REFL tm);
(* Reduce the application spine without visiting a continuation body. *)
fun head_beta_conv tm =
  if is_comb tm then
    (RATOR_CONV head_beta_conv THENC TRY_CONV planner_beta_conv) tm
  else REFL tm;
val finite_compset = relink_rules false
  [``dft_loop_run_fuel``, ``dft_block``, ``dfs_run_fuel``, ``dfs_step``,
   ``sort_children``, ``dft_cost``, ``build_offspring_map``,
   ``entry_instructions``, ``introduces_no_invoke_edges``] parity_compset
  |> computeLib.add_thms [listTheory.SET_TO_LIST_EMPTY]
  |> (fn cs => List.foldl
    (fn (c, current) => computeLib.set_skip current c (SOME 0)) cs
    (List.concat (map TypeBase.constructors_of
      [``:instruction``, ``:basic_block``, ``:ir_function``])))
  |> (fn cs => computeLib.set_skip cs ``COND`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``$/\`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``list_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``option_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``pair_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``dftDefs$dfs_work_item_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``venomInst$opcode_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``venomState$operand_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``sort_children`` (SOME 0))
  |> (fn cs => computeLib.set_skip cs ``dft_cost`` (SOME 0));
val finite_eval = computeLib.CBV_CONV finite_compset;
fun restricted_finite_eval stops = Lib.with_flag (computeLib.stoppers,
  SOME (fn c => List.exists (same_const c) stops)) finite_eval;
fun eval_finite_call c = CONV_TAC (call_conv c finite_eval);
val offspring_fold = ref (NONE : term option);
val offspring_finished = ref true;
fun OFFSPRING_OPEN_TAC (g as (_, w)) = let
  val (path, call) = locate (fn tm =>
    same_const ``build_offspring_map`` (#1 (strip_comb tm)) andalso
    length (#2 (strip_comb tm)) = 2) w
  val equation = REWR_CONV dftDefsTheory.build_offspring_map_def call
  val () = offspring_fold := SOME (hd (#2 (strip_comb (rhs (concl equation)))))
  val () = offspring_finished := false
in CONV_TAC (PATH_CONV path (fn _ => equation)) g end;
fun offspring_call tm = let val (head, args) = strip_comb tm in
  same_const ``FOLDL`` head andalso length args = 3 andalso
  (case !offspring_fold of SOME f => aconv f (hd args) | NONE => false)
end;
val offspring_equations = FIRST_CONV (map REWR_CONV
  (CONJUNCTS (SPEC_ALL listTheory.FOLDL)));
fun offspring_chunk 0 tm = REFL tm
  | offspring_chunk n tm =
      (offspring_equations THENC (fn result =>
        if offspring_call result then
          (RATOR_CONV (RAND_CONV finite_eval) THENC offspring_chunk (n - 1)) result
        else (offspring_finished := true; REFL result))) tm;
fun OFFSPRING_STEP_TAC (g as (_, w)) =
  if !offspring_finished then ALL_TAC g
  else if can (locate offspring_call) w then
    CONV_TAC (at_conv offspring_call (offspring_chunk 4)) g
  else ALL_TAC g;


fun eval_call_until c stops = CONV_TAC (call_conv c (restricted_eval stops));

(* One DFT worklist iteration, preserving the checked remainder of the loop. *)
val dft_loop_head = ``dft_loop_run_fuel``;
val dft_block_head = ``dft_block``;
fun loop_call head tm = same_const head (#1 (strip_comb tm)) andalso
  length (#2 (strip_comb tm)) = 3;

fun loop_iteration head equations stops = let
  fun unroll tm =
    if aconv (List.nth (#2 (strip_comb tm), 1)) ``0:num``
    then REWR_CONV (hd equations) tm
    else (RATOR_CONV (RAND_CONV numLib.num_CONV) THENC
          REWR_CONV (List.nth (equations, 1))) tm
in RATOR_CONV (RAND_CONV eval) THENC unroll THENC
   restricted_finite_eval (head :: stops) THENC
   (fn tm => if loop_call head tm then
       RAND_CONV (restricted_finite_eval stops) tm else REFL tm)
end;

val dft_iteration = loop_iteration dft_loop_head
  (CONJUNCTS dftDefsTheory.dft_loop_run_fuel_def) [dft_block_head];
fun DFT_STEP_TAC (g as (_, w)) = let
  val step = CONV_TAC (at_conv (loop_call dft_loop_head) dft_iteration)
in if has_term (loop_call dft_loop_head) w then step g else ALL_TAC g end;

fun DFT_BLOCK_TAC (g as (_, w)) = let
  fun is_block tm = same_const dft_block_head (#1 (strip_comb tm)) andalso
    length (#2 (strip_comb tm)) = 2 andalso null (free_vars tm)
in if has_term is_block w then eval_call dft_block_head g else ALL_TAC g end;

val EXEC_PASS_TAC = PARITY_OPEN_PASS_TAC >>
  eval_call ``execute_configured_fn_pass``;

val PASS_RESULT_TAC = PURE_REWRITE_TAC [optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV);

val DFT_GRAPH_TAC = eval_call_until ``dft_block``
  [``build_offspring_map``, ``entry_instructions``, ``schedule_from_entries``];

val DFT_FINISH_TAC = DFT_STEP_TAC >> DFT_STEP_TAC;
val dfs_loop_head = ``dfs_run_fuel``;
val dfs_sort_head = ``sort_children``;
val dfs_cost_head = ``dft_cost``;
val dfs_stack_selector = #accessor (#2 (valOf (List.find
  (fn (name, _) => name = "ds_stack") (TypeBase.fields_of ``:dfs_state``))));
val dfs_cost_equation = ref (NONE : thm option);
val dfs_step_equation = ref (NONE : thm option);
val dfs_cost_cache = ref ([] : (term * thm) list);
fun DFS_CONTEXT_TAC (g as (_, w)) = let
  val (_, call) = locate (loop_call dfs_loop_head) w
  val step = hd (#2 (strip_comb call))
  val fixed = List.foldl (fn (argument, func) => boolSyntax.mk_icomb (func, argument))
    dfs_cost_head (List.take (#2 (strip_comb step), 4))
  val variable = genvar (type_of fixed)
  val step_variable = genvar (type_of step)
  fun capture (h as (assumptions, _)) = let
    fun binding assumption =
      CONV_RULE (REWR_CONV markerTheory.Abbrev_def) (ASSUME assumption)
    val equation = valOf (List.find (fn th => is_var (lhs (concl th)) andalso
      type_of (lhs (concl th)) = type_of fixed)
      (List.mapPartial (total binding) assumptions))
    val () = dfs_cost_equation := SOME equation
    val () = dfs_cost_cache := []
  in ALL_TAC h end
  fun capture_step (h as (assumptions, _)) = let
    fun binding assumption =
      CONV_RULE (REWR_CONV markerTheory.Abbrev_def) (ASSUME assumption)
    val equation = valOf (List.find (fn th => is_var (lhs (concl th)) andalso
      type_of (lhs (concl th)) = type_of step)
      (List.mapPartial (total binding) assumptions))
    val () = dfs_step_equation := SOME equation
  in ALL_TAC h end
in (markerLib.ABBREV_TAC (mk_eq (variable, fixed)) >> capture >>
    markerLib.ABBREV_TAC (mk_eq (step_variable, step)) >> capture_step) g end;


(* Compose bounded evaluations instead of retraversing the whole goal at
   every DFS work item. The split follows from the normative FUNPOW model. *)
fun dfs_chunk tm = let
  val args = #2 (strip_comb tm)
  val fuel = numSyntax.int_of_term (List.nth (args, 1))
  val count = Int.min (1, fuel)
  val step_equation = valOf (!dfs_step_equation)
  val step_args = #2 (strip_comb (rhs (concl step_equation)))
  val split = ISPECL (step_args @ [numSyntax.term_of_int (fuel - count),
    numSyntax.term_of_int count, List.nth (args, 2)]) parity_dfs_split
  val concrete = CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV eval))) split
  val folded = CONV_RULE (PURE_REWRITE_CONV [SYM step_equation]) concrete
in (REWR_CONV folded THENC RAND_CONV
    (PURE_REWRITE_CONV [step_equation] THENC
     restricted_finite_eval [dfs_sort_head, dfs_cost_head])) tm end;
fun dfs_sort_call tm = let val (head, args) = strip_comb tm in
  (length args = 6 andalso
    (same_const head dfs_sort_head orelse same_const head dfs_cost_head)) orelse
  (length args = 2 andalso case !dfs_cost_equation of
     NONE => false | SOME equation => aconv head (lhs (concl equation)))
end;
(* QSORT asks for the same parent/child costs repeatedly. Reuse only exact
   queries whose cached equalities have already been checked by the kernel. *)
fun dfs_cost_conv tm =
  case List.find (fn (query, _) => aconv query tm) (!dfs_cost_cache) of
    SOME (_, theorem) => theorem
  | NONE => let
      val equation = valOf (!dfs_cost_equation)
      val applied = List.foldl (fn (argument, th) => AP_THM th argument)
        equation (#2 (strip_comb tm))
      val result = CONV_RULE (RAND_CONV finite_eval) applied
      val () = dfs_cost_cache := (tm, result) :: !dfs_cost_cache
    in result end;
val dfs_sort_conv = REWR_CONV dftDefsTheory.sort_children_def THENC
  (fn tm => PURE_REWRITE_CONV [SYM (valOf (!dfs_cost_equation))] tm) THENC
  restricted_finite_eval [dfs_sort_head, dfs_cost_head];
fun DFS_CHUNK_TAC (g as (_, w)) =
  case total (locate (loop_call dfs_loop_head)) w of
    NONE => ALL_TAC g
  | SOME (path, call) => let
      val state = rand call
    in case total (locate dfs_sort_call) state of
      SOME (inside, operation) => let
        val conversion = if same_const (#1 (strip_comb operation)) dfs_sort_head then
          dfs_sort_conv
          else if same_const (#1 (strip_comb operation)) dfs_cost_head then finite_eval
          else dfs_cost_conv
      in CONV_TAC (PATH_CONV (path ^ "r" ^ inside) conversion) g end
    | NONE => let
        val stack = boolSyntax.mk_icomb (dfs_stack_selector, state)
        val empty = rhs (concl
          (restricted_finite_eval [dfs_sort_head, dfs_cost_head] stack))
        val conversion = if listSyntax.is_nil empty then finite_eval
          else if can listSyntax.dest_cons empty then dfs_chunk
          else RAND_CONV (restricted_finite_eval [dfs_sort_head, dfs_cost_head])
      in CONV_TAC (PATH_CONV path conversion) g end
    end;
fun DFS_NORMALIZE_TAC (g as (_, w)) =
  case total (locate (loop_call dfs_loop_head)) w of
    NONE => ALL_TAC g
  | SOME (path, _) => CONV_TAC (PATH_CONV path (RAND_CONV
      (restricted_finite_eval [dfs_sort_head, dfs_cost_head]))) g;
fun DFS_FINISH_TAC (g as (_, w)) =
  if has_term (loop_call dfs_loop_head) w then
    CONV_TAC (at_conv (loop_call dfs_loop_head) finite_eval) g else ALL_TAC g;
val READY_OPEN_TAC = eval_call_until ``codegen_ready``
  [``canonical_param_prefix``, ``wf_function``, ``fn_inst_wf``, ``ssa_form``,
   ``def_dominates_uses``, ``single_use_form``, ``cfg_is_normalized``];
val dominance_head = ``def_dominates_uses``;
fun DOM_SUBGOAL_TAC (g as (_, w)) = let
  fun matches tm = same_const dominance_head (#1 (strip_comb tm)) andalso
    length (#2 (strip_comb tm)) = 1 andalso null (free_vars tm)
  val (_, check) = locate matches w
in SUBGOAL_THEN check (fn th => SUBST_ALL_TAC (EQT_INTRO th)) g end;
val EVERY_GOALS_TAC = CONV_TAC (RAND_CONV finite_eval) >>
  PURE_REWRITE_TAC [listTheory.EVERY_DEF] >>
  rpt conj_tac >> FIRST [ACCEPT_TAC TRUTH, CONV_TAC head_beta_conv];
fun ABBREV_EVERY_TAC (g as (_, w)) = let
  val predicate = rand (rator w)
  val name = mk_var ("available_check", type_of predicate)
in markerLib.ABBREV_TAC (mk_eq (name, predicate)) g end;
val dominance_compset = relink_rules true
  [``def_dominates_uses_exec``, ``def_available_at_exec``, ``phi_edge_uses_wf_exec``]
  (computeLib.copy parity_compset
   |> (fn cs => computeLib.scrub_const cs ``def_available_at_exec``)
   |> computeLib.add_thms [codegenReadyComputeTheory.def_available_at_exec_compute])
  |> (fn cs => List.foldl
    (fn (head, current) => computeLib.set_skip current head (SOME 0)) cs
    (List.concat (map TypeBase.constructors_of
      [``:instruction``, ``:basic_block``, ``:ir_function``, ``:operand``,
       ``:cfg_analysis``])))
  |> (fn cs => computeLib.set_skip cs ``COND`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``$/\`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``list_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``option_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``pair_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``venomState$operand_CASE`` (SOME 1));
val DOM_EVAL_TAC = CONV_TAC (computeLib.CBV_CONV dominance_compset);
val DOM_BRANCH_TAC =
  CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV eval))) >>
  CONV_TAC (FIRST_CONV (map REWR_CONV
    (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))));




end

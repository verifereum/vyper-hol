(* Bounded stack planning with checked context projections. *)
structure foldedValueParityAbiPlanLib :> foldedValueParityAbiPlanLib = struct
open HolKernel Parse boolLib bossLib boolTheory numLib
open foldedValueParityLib foldedValueParityAbiDftLib
open foldedValueParityAbiComputeTheory

fun argument_conv nargs position conversion =
  if position = nargs then RAND_CONV conversion
  else RATOR_CONV (argument_conv (nargs - 1) position conversion);
fun curried_arity ty = case total dom_rng ty of
  NONE => 0 | SOME (_, result) => 1 + curried_arity result;
val fuel_equations = FIRST_CONV (map REWR_CONV
  (CONJUNCTS (SPEC_ALL stackPlanGenTheory.generate_fn_plan_aux_fuel_def)));
val fuel_worklist_eval = ref eval;
fun fuel_step nargs worklist_position tm =
  if (case !computeLib.stoppers of NONE => false
      | SOME stop => stop (#1 (strip_comb tm))) then
    raise mk_HOL_ERR "foldedValueParityAbi" "fuel_step" "stopped"
  else (argument_conv nargs worklist_position (!fuel_worklist_eval) THENC
    argument_conv nargs 1 (TRY_CONV numLib.num_CONV) THENC fuel_equations) tm;

val ir_constructors = List.concat (map TypeBase.constructors_of
  [``:instruction``, ``:basic_block``, ``:ir_function``, ``:operand``,
   ``:dfg_analysis``, ``:cfg_analysis``, ``:string list df_state``]);

val configured_codegen_compset = computeLib.copy dominance_compset
  |> computeLib.add_thms [listTheory.SET_TO_LIST_EMPTY]
  |> (fn cs => List.foldl
    (fn (c, current) => computeLib.set_skip current c (SOME 0)) cs ir_constructors)
  |> (fn cs => computeLib.scrub_const cs ``operand_equiv``)
  |> (fn cs => computeLib.scrub_const cs ``normalize_operand``)
  |> computeLib.add_thms
    [dfgDefsTheory.normalize_operand_def, dfgDefsTheory.operand_equiv_def,
     parity_operand_equiv_refl]
  |> (fn cs => computeLib.set_skip cs ``operand_equiv`` (SOME 0))
  |> (fn cs => computeLib.scrub_const cs ``generate_block_plan``)
  |> computeLib.add_thms [stackPlanGenTheory.generate_block_plan_def]
  |> (fn cs => computeLib.scrub_const cs ``reduce_depth_plan``)
  |> (fn cs => computeLib.scrub_const cs ``generate_block_insts_plan``)
  |> computeLib.add_thms
    [stackPlanGenComputeTheory.reduce_depth_plan_compute,
     stackPlanGenComputeTheory.generate_block_insts_plan_compute]
  |> (fn cs => computeLib.scrub_const cs ``LET``)
  |> (fn cs => computeLib.scrub_const cs ``generate_fn_plan_aux_fuel``)
  |> (fn cs => computeLib.scrub_const cs ``generate_succs_plan_fuel``)
  |> computeLib.add_thms [boolTheory.LET_THM]
  |> (fn cs => computeLib.set_skip cs ``LET`` (SOME 0))
  |> (fn cs => computeLib.scrub_const cs ``UNCURRY``)
  |> (fn cs => computeLib.scrub_const cs ``pair_CASE``)
  |> computeLib.add_thms [parity_uncurry_compute, pairTheory.pair_case_thm]
  |> (fn cs => computeLib.set_skip cs ``UNCURRY`` (SOME 0))
  |> (fn cs => computeLib.set_skip cs ``option_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``pair_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``list_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``venomInst$opcode_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``venomState$operand_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``asmIR$stack_op_CASE`` (SOME 1))
  |> (fn cs => computeLib.set_skip cs ``asmIR$asm_inst_CASE`` (SOME 1))
  |> computeLib.add_conv (``generate_fn_plan_aux_fuel``, 8, fuel_step 8 6)
  |> computeLib.add_conv (``generate_succs_plan_fuel``, 10, fuel_step 10 8)
  |> (fn cs => computeLib.set_skip cs ``generate_fn_plan_aux_fuel`` (SOME 0))
  |> (fn cs => computeLib.set_skip cs ``generate_succs_plan_fuel`` (SOME 0))
  |> (fn cs => List.foldl
    (fn (head, current) => computeLib.set_skip current head (SOME 0)) cs
    [``generate_block_plan``, ``clean_stack_plan``, ``cleanup_frame_vars``,
     ``cleanup_max_transient``, ``generate_inst_plan``])
  |> (fn cs => computeLib.set_skip cs ``generate_block_insts_plan_acc`` (SOME 0));

val codegen_compset = relink_rules true
  [``generate_fn_plan_analyzed``, ``generate_fn_plan_aux_fuel``,
   ``generate_succs_plan_fuel``, ``generate_block_plan``,
   ``generate_block_insts_plan_acc``, ``generate_inst_plan``,
   ``cleanup_frame_vars``, ``cleanup_max_transient``, ``execute_plan``, ``assemble``]
  configured_codegen_compset
  |> (fn cs => List.foldl
    (fn (head, current) => computeLib.set_skip current head (SOME 0)) cs
    (ir_constructors @ [``operand_equiv``, ``LET``, ``UNCURRY``,
     ``generate_fn_plan_aux_fuel``, ``generate_succs_plan_fuel``,
     ``generate_block_plan``, ``clean_stack_plan``, ``cleanup_frame_vars``,
     ``cleanup_max_transient``, ``generate_inst_plan``,
     ``generate_block_insts_plan_acc``]))
  |> (fn cs => List.foldl
    (fn (head, current) => computeLib.set_skip current head (SOME 1)) cs
    [``COND``, ``$/\``, ``option_CASE``, ``pair_CASE``, ``list_CASE``,
     ``venomInst$opcode_CASE``, ``venomState$operand_CASE``,
     ``asmIR$stack_op_CASE``, ``asmIR$asm_inst_CASE``]);
val codegen_eval = computeLib.CBV_CONV codegen_compset;
val () = fuel_worklist_eval := codegen_eval;
val codegen_weak_eval = computeLib.WEAK_CBV_CONV codegen_compset;
(* Force mutable state values once between instructions. Keeping operand
   payloads lazy here lets later updates duplicate unevaluated expressions. *)
val state_compset = computeLib.copy codegen_compset
  |> (fn cs => List.foldl
    (fn (head, current) => computeLib.set_skip current head NONE) cs
    (List.concat (map TypeBase.constructors_of
      [``:operand``, ``:plan_state``, ``:spill_alloc``])));
val state_eval = computeLib.CBV_CONV state_compset;
fun codegen_call_conv c conversion = let
  val nargs = curried_arity (type_of c)
in at_conv (fn tm => same_const c (#1 (strip_comb tm)) andalso
     length (#2 (strip_comb tm)) = nargs) conversion end;
fun eval_codegen_call c = CONV_TAC (codegen_call_conv c codegen_eval);
fun restricted_codegen_eval stops = Lib.with_flag (computeLib.stoppers,
  SOME (fn c => List.exists (same_const c) stops))
  (computeLib.WEAK_CBV_CONV codegen_compset);
fun eval_codegen_until c stops = CONV_TAC
  (codegen_call_conv c (restricted_codegen_eval stops));
val plan_acc_head = ``generate_block_insts_plan_acc``;
fun plan_insts_conv tm =
  if can listSyntax.dest_list tm then REFL tm else codegen_weak_eval tm;
fun plan_ops_conv tm =
  if can listSyntax.dest_list tm then REFL tm
  else FIRST_CONV
    [listLib.REVERSE_CONV,
     RATOR_CONV (RAND_CONV listLib.REVERSE_CONV) THENC listLib.APPEND_CONV,
     listLib.APPEND_CONV, codegen_weak_eval] tm;
val plan_equations =
  [CONJUNCT1 (SPEC_ALL stackPlanGenComputeTheory.generate_block_insts_plan_acc_def),
   parity_plan_last, parity_plan_next];
fun plan_iteration tm =
  (* The empty-suffix equation discards all static analyses and the cursor.
     Apply it before doing any argument normalization. *)
  if listSyntax.is_nil (List.nth (#2 (strip_comb tm), 9)) then
    (REWR_CONV (hd plan_equations) THENC
     RAND_CONV (LAND_CONV
       (RAND_CONV plan_ops_conv THENC listLib.REVERSE_CONV))) tm
  else (argument_conv 12 9 codegen_eval THENC
    argument_conv 12 10 plan_insts_conv THENC
    argument_conv 12 11 state_eval THENC
    argument_conv 12 12 plan_ops_conv THENC
    FIRST_CONV (map REWR_CONV plan_equations) THENC
    REPEATC (REWR_CONV boolTheory.LET_THM THENC planner_beta_conv)) tm;
val plan_stops = [``generate_block_plan``, ``clean_stack_plan``,
  ``cleanup_frame_vars``, ``cleanup_max_transient``, plan_acc_head,
  ``generate_inst_plan``,
  ``generate_fn_plan_aux_fuel``, ``generate_succs_plan_fuel``,
  ``execute_plan``, ``assemble``];
val plan_calls = map (fn head => (head, curried_arity (type_of head)))
  (List.filter (fn c => not (same_const c ``execute_plan`` orelse
    same_const c ``assemble``)) plan_stops);
(* locate never enters lambda bodies. The four fixed context abbreviations
   may occur in exposed operations; their bindings need not be expanded here. *)
fun active_plan_call tm = let val (head, args) = strip_comb tm in
  List.exists (fn (c, nargs) => same_const c head andalso length args = nargs)
    plan_calls
end;
(* Unwrap one available result at a time. Normalizing the entire nest of
   continuations at a block return needlessly duplicates the large context. *)
val option_case_head = ``option_CASE``;
val pair_case_head = ``pair_CASE``;
val cond_head = ``COND``;
fun available_case tm = let
  val (head, args) = strip_comb tm
in case args of
    [value, _, _] =>
      (same_const head option_case_head andalso
        (optionSyntax.is_some value orelse optionSyntax.is_none value)) orelse
      (same_const head cond_head andalso (aconv value T orelse aconv value F))
  | [value, _] => same_const head pair_case_head andalso pairSyntax.is_pair value
  | _ => false
end;
val uncurry_head = ``UNCURRY``;
val let_head = ``LET``;
fun available_result tm = available_case tm orelse
  (is_comb tm andalso is_abs (rator tm)) orelse let
    val (head, args) = strip_comb tm
  in length args = 2 andalso
    (same_const head uncurry_head orelse
      (same_const head let_head andalso
       not (can (locate active_plan_call) (List.nth (args, 1)))))
  end;
val pure_result_case_conv = FIRST_CONV (planner_beta_conv :: map REWR_CONV
  (CONJUNCTS (SPEC_ALL optionTheory.option_case_def) @
   [pairTheory.pair_case_thm, parity_uncurry_compute, boolTheory.LET_THM] @
   CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) THENC head_beta_conv;
fun result_case_conv tm =
  if same_const let_head (#1 (strip_comb tm)) then
    (RAND_CONV (restricted_codegen_eval plan_stops) THENC pure_result_case_conv) tm
  else pure_result_case_conv tm;
(* Search for operations and available results together. Searching through a
   known result for an operation can force its large deferred state needlessly. *)
fun plan_operation tm = available_result tm orelse active_plan_call tm;
(* Instruction-local LET values are reused by several projections. Evaluate
   them once before substitution rather than duplicating their computations. *)
fun instruction_eval conversion tm = let
  fun restore () = ignore (computeLib.set_skip codegen_compset ``LET`` (SOME 0))
  val () = ignore (computeLib.set_skip codegen_compset ``LET`` NONE)
in (conversion tm before restore ()) handle ex => (restore (); raise ex) end;
(* Identity type instantiation materializes kernel substitution closures.
   Alpha conversion certifies that the formula is unchanged. Reify only the
   changed subterm so unchanged instructions and continuations stay shared. *)
fun materialize_conv tm = ALPHA tm
  (Term.inst [{redex = ``:'a``, residue = ``:'a``}] tm);
fun PLAN_NORMALIZE_TAC (g as (_, w)) =
  case total (locate plan_operation) w of
    NONE => CONV_TAC (restricted_codegen_eval plan_stops THENC materialize_conv) g
  | SOME (path, call) => if available_result call then
      CONV_TAC (PATH_CONV path (result_case_conv THENC materialize_conv)) g
    else ALL_TAC g;
(* Block cleanup is a separate phase from instruction planning. In particular,
   its whole-function frame analysis must not run inside an instruction step. *)
fun PLAN_STEP_TAC (g as (_, w)) =
  case total (locate plan_operation) w of
    NONE => ALL_TAC g
  | SOME (path, call) => if available_result call then ALL_TAC g else let
      val head = #1 (strip_comb call)
      val local_eval = restricted_codegen_eval
        (List.filter (not o same_const head) plan_stops)
      val conversion = if same_const head plan_acc_head then plan_iteration
        else if same_const head ``generate_block_plan`` then
          REWR_CONV stackPlanGenTheory.generate_block_plan_def
        else if same_const head ``generate_inst_plan`` then instruction_eval local_eval
        else local_eval
    in CONV_TAC (PATH_CONV path
      (CHANGED_CONV conversion THENC materialize_conv)) g end;


val plan_aux_head = ``generate_fn_plan_aux``;
fun plan_aux_call tm = same_const plan_aux_head (#1 (strip_comb tm)) andalso
  length (#2 (strip_comb tm)) = 7;
fun PLAN_CONTEXT_TAC position (g as (_, w)) = let
  val (_, call) = locate plan_aux_call w
  val value = List.nth (#2 (strip_comb call), position)
  val name = genvar (type_of value)
  fun install (h as (assumptions, _)) = let
    fun binding assumption = let
      val th = CONV_RULE (REWR_CONV markerTheory.Abbrev_def) (ASSUME assumption)
      val variable = lhs (concl th)
    in if is_var variable andalso type_of variable = type_of value then th
       else raise Fail "different abbreviation" end
    val equation = valOf (List.find (fn th =>
      type_of (lhs (concl th)) = type_of value)
      (List.mapPartial (total binding) assumptions))
    val variable = lhs (concl equation)
    val data = rhs (concl equation)
    fun add_projection accessor = let
      val generic = #1 (strip_comb (lhs (concl (SPEC_ALL accessor))))
      val query = boolSyntax.mk_icomb (generic, data)
      val selector = rator query
      val projected = TRANS (AP_TERM selector equation)
        (FIRST_CONV [REWR_CONV accessor, codegen_eval] query)
      fun conversion tm = if aconv (rand tm) variable then projected
        else raise mk_HOL_ERR "foldedValueParityAbi" "projection" "different context"
      fun register cs = ignore (computeLib.add_conv (selector, 1, conversion) cs)
    in app register [codegen_compset, state_compset] end
    val () = app add_projection (TypeBase.accessors_of (type_of value))
  in ALL_TAC h end
in (markerLib.ABBREV_TAC (mk_eq (name, value)) >> install) g end;

fun PLAN_FUEL_TAC (g as (_, w)) = let
  val (_, call) = locate plan_aux_call w
  val result = variant (free_vars w) (mk_var ("planner_result", type_of call))
  val continuation = mk_abs (result, subst [call |-> result] w)
  val transfer = ISPECL (``30:num`` :: #2 (strip_comb call) @ [continuation])
    parity_plan_fuel
in MATCH_MP_TAC (BETA_RULE transfer) g end;



end

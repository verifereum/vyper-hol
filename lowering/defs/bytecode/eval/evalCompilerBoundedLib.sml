(* Bounded, kernel-checked evaluation phases for larger compiler fixtures. *)
structure evalCompilerBoundedLib = struct
open HolKernel Parse boolLib bossLib
open boolTheory listTheory compileVyperTheory
open evalCompilerEntryLib
open evalCompilerPlanDataLib

(* Keep analysis and rename boundaries separate at the fixed tactic limit. *)
val entry_execute_pass = entry_stage "execute_configured_fn_pass"
val entry_ssa_open = simp_tac pure_ss
  [venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa,
   makeSsaCurrentDefsTheory.make_ssa_current_fn_def]
val entry_ssa_start = entry_pass_begin >> entry_ssa_open >>
  entry_stage "fn_entry_label" >> simp_tac pure_ss [optionTheory.option_case_def]
val entry_ssa_cfg = entry_analysis_stage "cfg_analyze"
val entry_ssa_dom = entry_analysis_stage "dom_analyze"
fun entry_compute_once name g = let
  fun selected tm = let val (h,args) = strip_comb tm in
    is_const h andalso #Name (dest_thy_const h) = name andalso
    List.length args = entry_function_arity (type_of h) andalso
    List.null (free_vars tm) end
  val target = find_term selected (lhs (snd g))
  val th = CHANGED_CONV (computeLib.WEAK_CBV_CONV (computeLib.the_compset())) target
in CONV_TAC (LAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV
     (fn t => if selected t andalso aconv t target then th else NO_CONV t)))) g end
val entry_dom_open = entry_eval_stage
  (SIMP_CONV pure_ss [dominatorDefsTheory.dom_analyze_def, LET_THM]) "dom_analyze"
val entry_dom_fixpoint = entry_compute_once "dom_fixpoint"
val entry_dom_sets = entry_compute_once "dom_sets_of"
val entry_dom_idom = entry_compute_once "compute_idom"
val entry_dom_dominated = entry_compute_once "compute_dominated"
val entry_dom_frontier = entry_compute_once "compute_df"
val entry_ssa_let = simp_tac pure_ss [Once LET_THM]
val entry_ssa_live = entry_analysis_stage "liveness_analyze"
val entry_ssa_phi = entry_stage "add_phi_nodes_supply"
val entry_ssa_rename = entry_stage "rename_current_blocks"
val entry_ssa_simplify = entry_stage "simplify_current_phis_if"
val entry_concretize_open = simp_tac pure_ss
  [venomPassDispatcherTheory.execute_configured_fn_pass_concretize]
val entry_concretize_start = entry_pass_begin >> entry_concretize_open
val entry_concretize_function = simp_tac pure_ss
  [concretizeMemLocDefsTheory.concretize_function_fuel_in_context_def]
val entry_concretize_layout = simp_tac pure_ss
  [OR_CLAUSES, COND_CLAUSES,
   concretizeMemLocDefsTheory.compute_function_layout_fuel_in_context_def]
val entry_allocation_open = entry_eval_stage
  (REWR_CONV concretizeMemLocDefsTheory.compute_alloc_map_fuel_in_context_def THENC
   SIMP_CONV pure_ss [Once LET_THM] THENC
   SIMP_CONV pure_ss [Once LET_THM] THENC
   SIMP_CONV pure_ss [Once LET_THM]) "compute_alloc_map_fuel_in_context"
val entry_allocation_finish_open = simp_tac pure_ss [LET_THM]


val entry_choose_grouped_path = simp_tac pure_ss [LET_THM, pairTheory.pair_case_thm,
    listTheory.MAP, combinTheory.o_DEF, external_has_defaults_def,
    listTheory.EXISTS_DEF, listTheory.NULL_DEF, NOT_CLAUSES,
    OR_CLAUSES, COND_CLAUSES] >> BETA_TAC
(* Unfold only the current DFS call. Stop before recursively visiting another
   edge or planning another block, including when that edge was already seen. *)
fun entry_plan_small_resume tm = let
  val (head,args) = strip_comb tm
  fun argument i n cv =
    if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  val work = case #Name (dest_thy_const head) of
      "generate_fn_plan_aux" => argument 4 (List.length args) (entry_plan_compute computeLib.EVAL_CONV) tm
    | "generate_succs_plan" => argument 6 (List.length args) (entry_plan_compute computeLib.EVAL_CONV) tm
    | _ => REFL tm
  val prepared = TRANS work (RAND_CONV (entry_plan_compute computeLib.EVAL_CONV) (rhs (concl work)))
  val equations = [stackPlanGenTheory.generate_fn_plan_analyzed_def,
    stackPlanGenTheory.generate_fn_plan_with_cleanup_analyzed_def] @
    List.map (fn n => cj n stackPlanGenTheory.generate_fn_plan_aux_def) [1,2,3,4]
  val unfolded = FIRST_CONV (List.map REWR_CONV equations) (rhs (concl prepared))
in TRANS prepared unfolded end
val entry_plan_small_once = entry_eval_stage_names entry_plan_small_resume
  entry_plan_driver_names
fun entry_plan_small_control g =
  if entry_has_block (lhs (snd g)) then ALL_TAC g
  else if entry_has_call entry_plan_driver_names
    (lhs (snd g)) then entry_plan_small_once g else ALL_TAC g
val plan_admin = entry_plan_spine_admin
open evalCompilerPlanCacheLib
val entry_instruction_compset = ref (NONE : computeLib.compset option)
fun plan_cache_vars g =
  (entry_instruction_compset := NONE; entry_plan_abbrev_defs := [];
   evalCompilerPlanCacheLib.plan_cache_vars g)
(* Canonicalize each shared record once, before summary-cache registration.
   Subsequent lazy projections then match the same immutable arguments. *)
fun entry_plan_normalize i = let
  fun normalize tm = let
    val (head,args) = strip_comb tm
    fun argument n cv = if n = List.length args - 1 then RAND_CONV cv
      else RATOR_CONV (argument (n+1) cv)
  in argument (entry_plan_argument_index head i) computeLib.EVAL_CONV tm end
in TRY (entry_eval_stage_names normalize entry_plan_analyzed_names) end
(* Follow the demanded case argument, without searching deferred continuations
   or traversing the complete analysis records just to locate a planner call. *)
fun entry_plan_active names evaluate tm = let
  val (head,args) = strip_comb tm
  val name = if is_const head then #Name (dest_thy_const head) else ""
  fun argument i n cv =
    if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
in if List.exists (fn target => name = target) names andalso
      List.length args = entry_function_arity (type_of head) then evaluate tm
   else case (name,List.length args) of
       ("option_CASE",3) => argument 0 3 (entry_plan_active names evaluate) tm
     | ("pair_CASE",2) => argument 0 2 (entry_plan_active names evaluate) tm
     | ("UNCURRY",2) => argument 1 2 (entry_plan_active names evaluate) tm
     | ("OPTION_MAP",2) => argument 1 2 (entry_plan_active names evaluate) tm
     | ("COND",3) => argument 0 3 (entry_plan_active names evaluate) tm
     | _ => NO_CONV tm
end
val plan_control = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active
    entry_plan_driver_names entry_plan_small_resume)))
val entry_plan_begin = CONV_TAC (LAND_CONV (CHANGED_CONV
  (entry_plan_active entry_plan_analyzed_names entry_plan_small_resume)))

(* One dominator-tree node or one child-list transition. The current block's
   instruction rename completes before the next recursive tree call begins. *)
fun entry_rename_step_conv tm = let
  val prepared = RAND_CONV computeLib.EVAL_CONV tm
  val equations = List.map
    (fn n => cj n makeSsaCurrentDefsTheory.rename_current_blocks_def) [1,2,3]
  val unfolded = FIRST_CONV (List.map REWR_CONV equations) (rhs (concl prepared))
  val cs = computeLib.set_skip (computeLib.copy (computeLib.the_compset()))
    boolSyntax.conditional (SOME 1)
    |> computeLib.add_thms [optionTheory.option_case_lazily]
  fun stop t = is_const t andalso List.exists
    (fn name => #Name (dest_thy_const t) = name)
    ["rename_current_blocks", "rename_current_children"]
  val evaluated = Lib.with_flag (computeLib.stoppers,SOME stop)
    (computeLib.WEAK_CBV_CONV cs) (rhs (concl unfolded))
in TRANS prepared (TRANS unfolded evaluated) end
val entry_rename_step = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["rename_current_blocks", "rename_current_children"]
    entry_rename_step_conv)))
val entry_rename_four = entry_rename_step >> entry_admin >>
  entry_rename_step >> entry_admin >> entry_rename_step >> entry_admin >>
  entry_rename_step >> entry_admin
fun entry_rename_finish g =
  if entry_has_call ["rename_current_blocks", "rename_current_children"] (lhs (snd g)) then
    raise Fail "SSA rename needs more finite tree boundaries"
  else ALL_TAC g

val entry_sue_open = simp_tac pure_ss
  [venomPassDispatcherTheory.execute_configured_fn_pass_sue,
   singleUseExpansionDefsTheory.sue_expand_function_supply_def]
val entry_sue_start = entry_pass_begin >> entry_sue_open
(* Unfold the traversal without running its recursive continuation. The next
   independently timed conversion evaluates only the current instruction. *)
fun entry_sue_block_step tm = let
  val prepared = RAND_CONV computeLib.EVAL_CONV tm
  val head = fst (strip_comb tm)
  val equations = if #Name (dest_thy_const head) = "sue_expand_blocks_supply"
    then singleUseExpansionDefsTheory.sue_expand_blocks_supply_def
    else singleUseExpansionDefsTheory.sue_expand_insts_supply_def
  val expanded = FIRST_CONV (List.map
    (fn n => REWR_CONV (cj n equations)) [1,2]) (rhs (concl prepared))
  val body = rhs (concl expanded)
  val opened = (SIMP_CONV pure_ss
    [singleUseExpansionDefsTheory.sue_expand_block_supply_def] body
    handle UNCHANGED => REFL body)
in TRANS prepared (TRANS expanded opened) end
val entry_sue_instruction = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["sue_expand_inst_supply"] computeLib.EVAL_CONV)))
fun entry_sue_tick g =
  if entry_has_call ["sue_expand_blocks_supply", "sue_expand_insts_supply"] (lhs (snd g)) then
    CONV_TAC (LAND_CONV (CHANGED_CONV (entry_plan_active
      ["sue_expand_blocks_supply", "sue_expand_insts_supply"] entry_sue_block_step))) g
  else ALL_TAC g
fun entry_sue_finish g =
  if entry_has_call ["sue_expand_blocks_supply", "sue_expand_insts_supply"] (lhs (snd g)) then
    raise Fail "single-use expansion needs more finite instruction boundaries"
  else ALL_TAC g
(* Stop at the block's instruction driver, then advance one instruction per
   phase. Immutable analysis/IR records are evaluated only when projected. *)
fun entry_plan_readonly_cs data_types = let
  fun lazy_type (ty,cs) = List.foldl
    (fn (ctor,acc) => computeLib.set_skip acc ctor (SOME 0)) cs
    (TypeBase.constructors_of ty)
in List.foldl lazy_type (computeLib.copy (computeLib.the_compset()))
  (data_types @ [``:instruction``, ``:basic_block``, ``:operand``]) end
fun entry_plan_data_cs tm = let
  val (_,args) = strip_comb tm
in entry_plan_readonly_cs
  (List.map type_of (List.take (args,Int.min (4,List.length args)))) end
val entry_plan_block_start = REWR_CONV stackPlanGenTheory.generate_block_plan_def
fun entry_plan_cleanup_guard tm = let
  val (_,args) = strip_comb tm
  fun selected t = let val (h,aa) = strip_comb t in
    is_const h andalso #Name (dest_thy_const h) = "cleanup_elision_safe" andalso
    List.length aa = entry_function_arity (type_of h) andalso entry_plan_closed t end
  val target = find_term selected (hd args)
  val cs = entry_plan_readonly_cs (List.map type_of (snd (strip_comb target)))
    |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
    |> computeLib.add_thms [optionTheory.option_case_lazily]
  val th = entry_plan_compute (entry_cached_cleanup (computeLib.WEAK_CBV_CONV cs)) target
in RATOR_CONV (RATOR_CONV (RAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV
     (fn t => if aconv t target then th else NO_CONV t))))) tm end
(* Evaluate one setup condition or one frame/parameter operation. Retain the
   block's instruction traversal for the separately timed instruction phases. *)
fun entry_plan_setup tm = let
  val (head,args) = strip_comb tm
  val name = #Name (dest_thy_const head)
in if name = "COND" then
     if entry_plan_has_call ["spill_plan_in_region"] (hd args) then NO_CONV tm
     else if entry_plan_has_call ["cleanup_elision_safe"] (hd args) then
       entry_plan_cleanup_guard tm
     else (RATOR_CONV (RATOR_CONV (RAND_CONV (entry_plan_compute computeLib.EVAL_CONV))) THENC
       PURE_REWRITE_CONV [COND_CLAUSES]) tm
   else if name = "clean_stack_plan" orelse name = "prepare_params_plan" then let
     val count = if name = "clean_stack_plan" then 4 else 2
     val cs = entry_plan_readonly_cs (List.map type_of (List.take (args,count)))
       |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
       |> computeLib.add_thms [optionTheory.option_case_lazily]
     fun stop t = is_const t andalso
       #Name (dest_thy_const t) = "cleanup_elision_safe"
   in entry_plan_compute (Lib.with_flag (computeLib.stoppers,SOME stop)
        (computeLib.WEAK_CBV_CONV cs)) tm end
   else entry_plan_compute computeLib.EVAL_CONV tm
end
val plan_setup = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["COND", "prepare_params_plan", "clean_stack_plan",
     "lookup_block", "fn_entry_label"]
    entry_plan_setup)))
fun entry_plan_inst_step tm = let
  val (_,args) = strip_comb tm
  fun argument i n cv =
    if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  val prepared = argument 9 (List.length args) (entry_plan_compute computeLib.EVAL_CONV) tm
  val expanded = FIRST_CONV (List.map
    (fn n => REWR_CONV (cj n stackPlanGenTheory.generate_block_insts_plan_def))
    [1,2]) (rhs (concl prepared))
in TRANS prepared expanded end
fun entry_plan_instruction_cs tm = case !entry_instruction_compset of
    SOME cs => cs
  | NONE => let
      val cs = entry_plan_data_cs tm
        |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
        |> computeLib.add_thms [optionTheory.option_case_lazily]
      val () = entry_instruction_compset := SOME cs
    in cs end
(* Evaluate only the instruction's small, changing arguments at a separate
   boundary; the four immutable analysis/function arguments remain shared. *)
fun entry_plan_inputs tm = let
  val evaluate = entry_plan_compute (computeLib.WEAK_CBV_CONV (entry_plan_instruction_cs tm))
  fun argument i n cv =
    if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
in EVERY_CONV (List.map (fn i => argument i 10 evaluate) [4,5,6,7,8,9]) tm end
val plan_inputs = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["generate_inst_plan"] entry_plan_inputs)))
fun entry_plan_instruction tm = let
  val cs = entry_plan_instruction_cs tm
  val th = entry_plan_compute (computeLib.WEAK_CBV_CONV cs) tm
  val () = if optionSyntax.is_none (rhs (concl th)) then
    raise Fail "instruction planning failed" else ()
in th end
val plan_instruction = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["generate_inst_plan"] entry_plan_instruction)))
fun entry_plan_block_phase tm =
  if #Name (dest_thy_const (fst (strip_comb tm))) = "generate_block_plan"
  then entry_plan_block_start tm else entry_plan_inst_step tm
val plan_block = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["generate_block_plan", "generate_block_insts_plan"]
    entry_plan_block_phase)))
val plan_step = plan_control >> plan_admin >> plan_block >> plan_admin >> plan_setup >>
  plan_instruction >> plan_admin
val plan_four = plan_step >> plan_step >> plan_step >> plan_step
fun plan_finish g =
  if entry_plan_has_call (entry_plan_driver_names @
      ["generate_block_plan", "generate_block_insts_plan",
       "generate_inst_plan", "prepare_params_plan", "clean_stack_plan",
       "cleanup_elision_safe"])
      (lhs (snd g)) then
    raise Fail "planner needs more finite instruction/control boundaries"
  else ALL_TAC g

fun entry_plan_compact_dfg g = let
  fun selected tm = let val (h,args) = strip_comb tm in
    entry_is_analyzed h andalso
    List.length args = entry_function_arity (type_of h) andalso
    List.null (free_vars tm) end
  val target = find_term selected (lhs (snd g))
  val (_,args) = strip_comb target
  fun argument i n cv = if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  val th = argument 1 (List.length args) entry_compact_maps target
in CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV
     (fn t => if aconv t target then th else NO_CONV t))) g end

val entry_open_dfg = simp_tac pure_ss
  [dfgDefsTheory.dfg_build_function_def, dfgDefsTheory.dfg_build_insts_def]
val entry_dfg_compset = entry_plan_readonly_cs [``:instruction``]
fun entry_dfg_prefix evaluate 0 tm = REFL tm
  | entry_dfg_prefix evaluate n tm = FIRST_CONV
      [REWR_CONV (cj 1 dfgDefsTheory.dfg_build_insts_rev_def),
       REWR_CONV (cj 2 dfgDefsTheory.dfg_build_insts_rev_def) THENC
        RATOR_CONV (RAND_CONV evaluate) THENC
        entry_dfg_prefix evaluate (n-1)] tm
fun entry_dfg_tick g =
  if entry_has_call ["dfg_build_insts_rev"] (lhs (snd g)) then
    entry_eval_stage (RAND_CONV computeLib.EVAL_CONV THENC
      entry_dfg_prefix (computeLib.CBV_CONV entry_dfg_compset) 4)
      "dfg_build_insts_rev" g
  else ALL_TAC g
fun entry_dfg_finish g =
  if entry_has_call ["dfg_build_insts_rev"] (lhs (snd g)) then
    raise Fail "DFG construction needs more finite instruction boundaries"
  else ALL_TAC g

val entry_pass_effects = entry_guard "fn_pass_effects_hold" >>
  entry_guard "introduces_no_invoke_edges"
val entry_supply_extends = entry_guard "ir_supply_extends"
val entry_supply_function = entry_guard "ir_supply_covers_fn"
val entry_supply_unit = entry_guard "ir_supply_covers_unit"

val entry_dft_open = simp_tac pure_ss
  [venomPassDispatcherTheory.execute_configured_fn_pass_dft]
val entry_dft_function_open = entry_eval_stage
  (REWR_CONV dftDefsTheory.dft_fn_compute) "dft_fn"
val entry_dft_start = entry_pass_begin >> entry_dft_open >> entry_dft_function_open
val entry_dft_cfg = entry_analysis_stage "cfg_analyze" >> simp_tac pure_ss [Once LET_THM]
val entry_dft_live = entry_analysis_stage "liveness_analyze"
(* Advance one real DFT worklist iteration, retaining the driver's fuel. *)
fun entry_dft_step_conv tm = let
  val prepared = (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV) THENC
    RAND_CONV computeLib.EVAL_CONV) tm
  val body = rhs (concl prepared)
  val (_,args) = strip_comb body
  val (_,rest) = pairSyntax.dest_pair (List.nth (args,2))
  val (_,finished) = pairSyntax.dest_pair rest
  val evaluated =
    if aconv finished boolSyntax.T then
      SIMP_CONV pure_ss [dftDefsTheory.dft_loop_run_fuel_done, pairTheory.SND] body
    else if numSyntax.dest_numeral (List.nth (args,1)) = Arbnum.zero then
      REWR_CONV (cj 1 dftDefsTheory.dft_loop_run_fuel_def) body
    else
      (RATOR_CONV (RAND_CONV numLib.num_CONV) THENC
       REWR_CONV (cj 2 dftDefsTheory.dft_loop_run_fuel_def) THENC
       RATOR_CONV (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV)) THENC
       PURE_REWRITE_CONV [COND_CLAUSES] THENC
       RAND_CONV computeLib.EVAL_CONV) body
in TRANS prepared evaluated end
fun entry_dft_tick g =
  if entry_has_call ["dft_loop_run_fuel"] (lhs (snd g)) then
    entry_eval_stage entry_dft_step_conv "dft_loop_run_fuel" g
  else ALL_TAC g
fun entry_dft_finish g =
  if entry_has_call ["dft_loop_run_fuel"] (lhs (snd g)) then
    raise Fail "DFT worklist needs more checked iteration boundaries"
  else ALL_TAC g

val entry_ml_open = entry_eval_stage
  (REWR_CONV concretizeMemLocDefsTheory.mem_liveness_analyze_fuel_def)
  "mem_liveness_analyze_fuel"
(* Execute one real fixed-point pass, then select its continuation without
   evaluating that continuation. Preserve the original remaining fuel. *)
fun entry_ml_step_conv tm = let
  fun argument i n cv =
    if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  val prepared = argument 0 9 computeLib.EVAL_CONV tm
  val body = rhs (concl prepared)
  val fuel = hd (snd (strip_comb body))
  val step = if numSyntax.dest_numeral fuel = Arbnum.zero then
      REWR_CONV (cj 1 concretizeMemLocDefsTheory.ml_iterate_fuel_def) body
    else let
      val unfolded = (argument 0 9 numLib.num_CONV THENC
        REWR_CONV (cj 2 concretizeMemLocDefsTheory.ml_iterate_fuel_def)) body
      fun selected t = let val (h,args) = strip_comb t in
        is_const h andalso #Name (dest_thy_const h) = "ml_one_pass" andalso
        List.length args = entry_function_arity (type_of h) andalso
        List.null (free_vars t) end
      val target = find_term selected (rhs (concl unfolded))
      val pass = computeLib.WEAK_CBV_CONV (computeLib.the_compset()) target
      val (changed,_) = pairSyntax.dest_pair (rhs (concl pass))
      val () = if aconv changed boolSyntax.T orelse aconv changed boolSyntax.F
        then () else raise Fail "incomplete memory-liveness pass"
      val evaluated = CHANGED_CONV (ONCE_DEPTH_CONV
        (fn t => if selected t andalso aconv t target then pass else NO_CONV t))
        (rhs (concl unfolded))
      val resumed = entry_plan_spine_conv (rhs (concl evaluated))
    in TRANS unfolded (TRANS evaluated resumed) end
in TRANS prepared step end
fun entry_ml_tick g =
  if entry_has_call ["ml_iterate_fuel"] (lhs (snd g)) then
    entry_eval_stage entry_ml_step_conv "ml_iterate_fuel" g
  else ALL_TAC g
fun entry_ml_finish g =
  if entry_has_call ["ml_iterate_fuel"] (lhs (snd g)) then
    raise Fail "memory liveness needs more finite iteration boundaries"
  else ALL_TAC g
val entry_closed_pair_let = CONV_TAC (LAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV
  (fn tm => let
    val (h,args) = strip_comb tm
    val name = if is_const h then #Name (dest_thy_const h) else ""
    val value = case (name,List.length args) of
        ("LET",2) => SOME (List.nth(args,1))
      | ("UNCURRY",2) => SOME (List.nth(args,1))
      | ("pair_CASE",2) => SOME (List.nth(args,0))
      | _ => NONE
  in if Option.isSome value andalso pairSyntax.is_pair (valOf value) andalso
       List.null (free_vars tm) then entry_plan_spine_conv tm else NO_CONV tm
  end))))

val entry_open_pipeline = simp_tac pure_ss [NOT_CLAUSES, OR_CLAUSES, COND_CLAUSES,
    optionTheory.option_case_def, checked_unit_pipeline_def] >>
  simp_tac pure_ss [venomPipelineDriverTheory.run_venom_pipeline_def]
val entry_open_schedule = simp_tac pure_ss [venomPipelineRunnerTheory.run_callee_first_def,
    venomPipelineRunnerTheory.run_named_fn_schedules_def,
    venomFnScheduleRunnerTheory.run_configured_fn_passes_def]
val entry_open_codegen = simp_tac pure_ss [codegenTheory.finalize_codegen_identity,
     codegenTheory.codegen_assembly_def]
val entry_open_plan = simp_tac pure_ss [stackPlanGenTheory.generate_context_plan_def,
     LET_THM, stackPlanGenTheory.generate_context_plan_with_def] >>
  entry_stage "fcg_analyze" >> entry_stage "cleanup_growth_table"
val entry_open_region = simp_tac pure_ss [Once stackPlanGenTheory.generate_context_regions_def,
     stackPlanGenTheory.generate_fn_plan_def,
     stackPlanGenTheory.generate_fn_plan_with_cleanup_def] >>
  entry_stage "cleanup_caller_height"

val entry_open_codegen_ready = simp_tac pure_ss
  ([stackPlanGenTheory.codegen_ready_def, stackPlanGenTheory.codegen_ready_fn_def,
    listTheory.EVERY_DEF, combinTheory.K_THM] @
   #rewrs (TypeBase.simpls_of ``:venom_context``))

val entry_open_dominance = simp_tac pure_ss
  [codegenReadyComputeTheory.def_dominates_uses_compute]
val entry_open_dominance_exec = simp_tac pure_ss
  [COND_CLAUSES, codegenReadyComputeTheory.def_dominates_uses_exec_def]
(* Evaluate one basic block of the finite dominance check per boundary. *)
fun entry_dominance_every tm = let
  val (h,args) = strip_comb tm
  fun marker t = is_const t andalso
    List.exists (fn name => #Name (dest_thy_const t) = name)
      ["phi_edge_uses_wf_exec", "def_available_at_exec"]
in is_const h andalso #Name (dest_thy_const h) = "EVERY" andalso
   List.length args = 2 andalso List.null (free_vars tm) andalso
   can (find_term marker) (hd args)
end
fun entry_dominance_tick g =
  case total (find_term entry_dominance_every) (lhs (snd g)) of
    NONE => ALL_TAC g
  | SOME target => CONV_TAC (LAND_CONV (fn tm => let
      val th = (RAND_CONV computeLib.EVAL_CONV THENC FIRST_CONV
        [REWR_CONV (cj 1 listTheory.EVERY_DEF),
         REWR_CONV (cj 2 listTheory.EVERY_DEF) THENC
         LAND_CONV computeLib.EVAL_CONV THENC
         PURE_REWRITE_CONV [AND_CLAUSES]]) target
    in CHANGED_CONV (ONCE_DEPTH_CONV (fn t => if aconv t target then th else NO_CONV t)) tm end)) g
fun entry_dominance_finish g =
  if can (find_term entry_dominance_every) (lhs (snd g)) then
    raise Fail "dominance check needs more basic-block boundaries"
  else ALL_TAC g

val entry_open_single_use = simp_tac pure_ss [passSharedDefsTheory.single_use_form_compute]
fun entry_single_use_every tm = let
  val (h,args) = strip_comb tm
  fun marker t = is_const t andalso #Name (dest_thy_const t) = "var_use_count_block"
in is_const h andalso #Name (dest_thy_const h) = "EVERY" andalso
   List.length args = 2 andalso List.null (free_vars tm) andalso
   can (find_term marker) (hd args)
end
(* Check a fixed finite prefix, retaining the exact residual EVERY judgment. *)
fun entry_single_use_prefix 0 tm = REFL tm
  | entry_single_use_prefix n tm = FIRST_CONV
      [REWR_CONV (cj 1 listTheory.EVERY_DEF),
       REWR_CONV (cj 2 listTheory.EVERY_DEF) THENC
       LAND_CONV computeLib.EVAL_CONV THENC
       RAND_CONV (entry_single_use_prefix (n-1)) THENC
       PURE_REWRITE_CONV [AND_CLAUSES]] tm
fun entry_single_use_chunk g =
  case total (find_term entry_single_use_every) (lhs (snd g)) of
    NONE => ALL_TAC g
  | SOME target => let
      val th = (RAND_CONV computeLib.EVAL_CONV THENC entry_single_use_prefix 8) target
    in CONV_TAC (LAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV
         (fn t => if aconv t target then th else NO_CONV t)))) g end
fun entry_single_use_finish g =
  if can (find_term entry_single_use_every) (lhs (snd g)) then
    raise Fail "single-use check needs more finite-prefix boundaries"
  else ALL_TAC g

end

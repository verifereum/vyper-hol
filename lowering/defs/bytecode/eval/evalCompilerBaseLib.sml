(* Checked evaluation support for the multi-function external-entry base. *)
structure evalCompilerBaseLib = struct
open HolKernel Parse boolLib bossLib boolTheory
open evalCompilerEntryLib evalCompilerGuardLib evalCompilerFlowLib
     evalCompilerBoundedLib evalCompilerFlowStepLib

(* Reduce each supply projection once, before EVERY captures its bound.
   Leave unit/function payloads alone while locating those projections. *)
val base_supply_cs = entry_plan_readonly_cs [``:ir_supply``]
fun base_supply_projections tm = let
  val (h,args) = strip_comb tm
in if is_const h andalso List.length args = 1 andalso
      entry_function_arity (type_of h) = 1 andalso
      type_of (hd args) = ``:ir_supply`` andalso List.null (free_vars tm)
   then computeLib.WEAK_CBV_CONV base_supply_cs tm
   else if List.exists (fn ty => type_of tm = ty)
      [``:compilation_unit``, ``:venom_context``, ``:ir_function``, ``:ir_supply``]
   then REFL tm else SUB_CONV base_supply_projections tm
end
fun base_supply_open name definition = flow_named name
  (REWR_CONV definition THENC base_supply_projections)
val supply_extends_open = base_supply_open "ir_supply_extends"
  venomFnScheduleRunnerTheory.ir_supply_extends_def
val supply_le_name = #Name (dest_thy_const (fst (strip_comb ``0n <= 0n``)))
fun supply_counters g =
  if entry_has_call [supply_le_name] (lhs (snd g)) then entry_guard supply_le_name g
  else ALL_TAC g
val function_supply_open = base_supply_open "ir_supply_covers_fn"
  venomFnScheduleRunnerTheory.ir_supply_covers_fn_def
val unit_supply_open = base_supply_open "ir_supply_covers_unit"
  venomFnScheduleRunnerTheory.ir_supply_covers_unit_def
val base_let = flow_named "LET"
  (REWR_CONV LET_THM THENC TRY_CONV BETA_CONV)
(* Consume a computed option without simplifying deferred compiler branches. *)
val base_option_some = flow_transform
  (fn tm => flow_call "option_CASE" tm andalso
    optionSyntax.is_some (hd (snd (strip_comb tm))))
  (REWR_CONV (cj 2 optionTheory.option_case_def) THENC TRY_CONV BETA_CONV)
(* Expose the SSA entry-label binding at its constructor case. *)
fun base_ssa_label_case tm =
  if flow_call "option_CASE" tm then let
    val (_,args) = strip_comb tm
    fun cfg_call t = let val h = fst (strip_comb t) in
      is_const h andalso #Name (dest_thy_const h) = "cfg_analyze" end
  in type_of (hd args) = ``:string option`` andalso
     optionSyntax.is_some (hd args) andalso
     can (find_term cfg_call) (List.nth(args,2))
  end else false
val base_ssa_label = flow_transform base_ssa_label_case
  (FIRST_CONV (List.map REWR_CONV
     (Drule.BODY_CONJUNCTS optionTheory.option_case_def)) THENC
   TRY_CONV BETA_CONV)
val base_dom_open = flow_named "dom_analyze"
  (REWR_CONV dominatorComputeTheory.dom_analyze_compute)
val base_dom_flow_open = flow_named "dom_fixpoint"
  (REWR_CONV dominatorComputeTheory.dom_fixpoint_compute)
val base_flow_compact = TRY (flow_named "wl_iterate"
  (RAND_CONV entry_compact_maps))
(* One original memory-liveness iteration, with its two scans separated. *)
(* Lift at the first selected call, rather than visiting every deferred branch.
   An identity normalization still identifies that call successfully. *)
fun base_first_conv selected evaluate tm = let
  fun locate t =
    if selected t then SOME []
    else if is_comb t then let
      val (h,args) = strip_comb t
      val active_let = is_const h andalso #Name (dest_thy_const h) = "LET"
        andalso List.length args = 2
      val (first,second) = if active_let then ((1,rand t),(0,rator t))
        else ((0,rator t),(1,rand t))
      fun descend (direction,child) =
        Option.map (fn path => direction :: path) (locate child)
    in case descend first of NONE => descend second | path => path end
    else if is_abs t then
      Option.map (fn path => 2 :: path) (locate (snd (dest_abs t)))
    else NONE
  fun at [] = evaluate
    | at (0 :: path) = RATOR_CONV (at path)
    | at (1 :: path) = RAND_CONV (at path)
    | at (_ :: path) = ABS_CONV (at path)
in case locate tm of NONE => NO_CONV tm | SOME path => at path tm end
fun base_eval_stage evaluate name = CONV_TAC
  (LAND_CONV (base_first_conv (flow_call name) (fn tm =>
    case !computeLib.stoppers of
        NONE => evaluate tm
      | SOME _ => raise Fail "unexpected stopper at a Base computation boundary")))
val base_native_stage = base_eval_stage
  (fn tm => computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm)
fun base_boolean_conv evaluate name tm = let
  val th = Conv.QCONV evaluate tm
  val result = rhs (concl th)
in if aconv result boolSyntax.T orelse aconv result boolSyntax.F then th
   else raise Fail ("incomplete Base guard: " ^ name)
end
fun base_native_guard name =
  base_eval_stage (base_boolean_conv computeLib.EVAL_CONV name) name
val base_supply_compset = List.foldl
  (fn (ctor,cs) => computeLib.set_skip cs ctor (SOME 0))
  (computeLib.copy evalCompilerSupplyLib.supply_compset)
  (TypeBase.constructors_of ``:fn_pass_output``)
fun base_supply_guard name = base_eval_stage
  (base_boolean_conv (computeLib.CBV_CONV base_supply_compset) name) name
val pass_effects = base_supply_guard "fn_pass_effects_hold"
val pass_calls = base_supply_guard "introduces_no_invoke_edges"
(* The unit check has four independent conjuncts. Check each at its own
   boundary, retaining the original formula and literal Boolean verdict. *)
val base_supply_unit_equation = ref (NONE : thm option)
fun base_supply_unit_open g = let
  val target = find_term (flow_call "ir_supply_covers_unit") (lhs (snd g))
  val equation = REWR_CONV
    venomFnScheduleRunnerTheory.ir_supply_covers_unit_def target
in base_supply_unit_equation := SOME equation; ALL_TAC g end
fun base_supply_unit_part i g = let
  val equation = valOf (!base_supply_unit_equation)
  val boolean = base_boolean_conv (computeLib.CBV_CONV base_supply_compset)
    "ir_supply_covers_unit conjunct"
  fun check tm = let
    val prepared = if flow_call "EVERY" tm then
        RATOR_CONV (RAND_CONV (ABS_CONV
          (RAND_CONV (computeLib.CBV_CONV base_supply_compset)))) tm
      else REFL tm
  in TRANS prepared (boolean (rhs (concl prepared))) end
  fun clause n tm =
    if boolSyntax.is_conj tm then
      (if n = 0 then LAND_CONV check else RAND_CONV (clause (n - 1))) tm
    else if n = 0 then check tm
    else raise Fail "missing unit supply conjunct"
  val checked = TRANS equation (clause i (rhs (concl equation)))
in if i < 3 then (base_supply_unit_equation := SOME checked; ALL_TAC g)
   else let
     val finished = TRANS checked
       (SIMP_CONV pure_ss [AND_CLAUSES] (rhs (concl checked)))
     val result = rhs (concl finished)
     val () = if aconv result boolSyntax.T orelse aconv result boolSyntax.F
       then () else raise Fail "unit supply check remained symbolic"
     val target = lhs (concl finished)
     val () = base_supply_unit_equation := NONE
   in CONV_TAC (LAND_CONV
        (base_first_conv (aconv target) (K finished))) g end
end
fun base_analysis_stage name = base_eval_stage (fn tm => let
  val th = computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm
in TRANS th (Conv.QCONV entry_compact_maps (rhs (concl th))) end) name
val base_fmp_dispatch = base_eval_stage
  (REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_fmp)
  "execute_configured_fn_pass"
val base_fmp_open = base_eval_stage
  (REWR_CONV fmpLowerDefsTheory.fmp_lower_function_def) "fmp_lower_function"
val base_fmp_body_open = base_eval_stage
  (REWR_CONV fmpLowerDefsTheory.fmp_lower_function_with_info_def)
  "fmp_lower_function_with_info"
val base_ssa_dispatch = base_eval_stage
  (REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa)
  "execute_configured_fn_pass"
val base_ssa_open = base_eval_stage
  (REWR_CONV makeSsaCurrentDefsTheory.make_ssa_current_fn_def) "make_ssa_current_fn"
val base_dft_dispatch = base_eval_stage
  (REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_dft)
  "execute_configured_fn_pass"
val base_dft_function_open = base_eval_stage
  (REWR_CONV dftDefsTheory.dft_fn_compute) "dft_fn"
val base_cfg_dispatch = base_eval_stage
  (REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg)
  "execute_configured_fn_pass"
val base_fmp_reclaim_cs = computeLib.copy (computeLib.the_compset())
  |> computeLib.add_thms [fmpReclaimDefsTheory.analyze_fmp_reclaims_def]
val base_fmp_reclaims = base_eval_stage (fn tm => let
  val th = Conv.QCONV (computeLib.CBV_CONV base_fmp_reclaim_cs) tm
  val result = rhs (concl th)
  val () = if optionSyntax.is_some result orelse optionSyntax.is_none result then ()
    else raise Fail "FMP reclaim analysis remained symbolic"
in TRANS th (Conv.QCONV entry_compact_maps result) end) "analyze_fmp_reclaims"
(* Keep SSA dominator results shared until each dependent binding is ready. *)
val base_ssa_dom_open = base_eval_stage
  (REWR_CONV dominatorDefsTheory.dom_analyze_def) "dom_analyze"
val base_dom_cs = entry_plan_readonly_cs
  [``:ir_function``, ``:cfg_analysis``, ``:fn_pass_output``, ``:ir_supply``,
   ``:compilation_unit``, ``:venom_context``]
val base_current_cs = computeLib.copy base_dom_cs |> computeLib.add_thms
  [venomFnScheduleRunnerTheory.unit_with_current_fn_def,
   venomFnScheduleRunnerTheory.replace_unique_function_def]
val base_current_function = base_eval_stage
  (computeLib.WEAK_CBV_CONV base_current_cs) "unit_with_current_fn"
val base_ssa_input = base_eval_stage (RAND_CONV
  (computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV))
  "make_ssa_current_fn"
val base_ssa_supply_input = base_eval_stage (RATOR_CONV (RAND_CONV
  (computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV)))
  "make_ssa_current_fn"
val base_dft_input = base_eval_stage (RAND_CONV
  (computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV)) "dft_fn"
val base_cfg_input = base_eval_stage (RAND_CONV
  (computeLib.WEAK_CBV_CONV base_dom_cs THENC computeLib.EVAL_CONV))
  "simplify_cfg_fn_with_labels"
fun base_fmp_input i = let
  fun argument n cv = if n = 3 then RAND_CONV cv
    else RATOR_CONV (argument (n + 1) cv)
  fun normalize tm = let
    val projected = computeLib.WEAK_CBV_CONV base_dom_cs tm
  in TRANS projected (Conv.QCONV computeLib.EVAL_CONV (rhs (concl projected))) end
in base_eval_stage (argument i normalize) "fmp_lower_function_with_info" end
val base_ssa_dom_input = base_eval_stage
  (RAND_CONV (computeLib.WEAK_CBV_CONV base_dom_cs)) "dom_analyze"
val base_ssa_dom_flow_open = base_eval_stage
  (REWR_CONV dominatorComputeTheory.dom_fixpoint_compute) "dom_fixpoint"
val base_ssa_flow_open = base_eval_stage
  (REWR_CONV dfAnalyzeDefsTheory.df_analyze_def) "df_analyze"
val base_dom_state_bind = CONV_TAC (LAND_CONV (base_first_conv
  (fn tm => let val (h,args) = strip_comb tm in
    is_const h andalso #Name (dest_thy_const h) = "LET" andalso
    List.length args = 2 andalso flow_state_type (List.nth (args,1)) andalso
    List.null (free_vars (List.nth (args,1))) end)
  (RAND_CONV entry_compact_maps THENC REWR_CONV LET_THM THENC
   TRY_CONV BETA_CONV)))
val base_live_input = base_eval_stage
  (RAND_CONV (computeLib.WEAK_CBV_CONV base_dom_cs)) "liveness_analyze"
val base_live_flow_open = base_eval_stage
  (REWR_CONV livenessDefsTheory.liveness_analyze_def THENC
   REWR_CONV livenessDefsTheory.liveness_recompute_def) "liveness_analyze"
fun base_dom_binding name = let
  val actual_name = case List.find (fn (field,_) => field = name)
      (TypeBase.fields_of ``:cfg_analysis``) of
      SOME (_, {accessor,...}) => #Name (dest_thy_const accessor)
    | NONE => name
  fun selected tm = let val (h,args) = strip_comb tm in
    is_const h andalso #Name (dest_thy_const h) = "LET" andalso
    List.length args = 2 andalso flow_call actual_name (List.nth (args,1))
  end
  fun value tm = let
    val th = computeLib.WEAK_CBV_CONV base_dom_cs tm
  in TRANS th (Conv.QCONV entry_compact_maps (rhs (concl th))) end
in CONV_TAC (LAND_CONV (base_first_conv selected
  (RAND_CONV value THENC REWR_CONV LET_THM THENC TRY_CONV BETA_CONV))) end
val base_ml_cs = entry_plan_readonly_cs [``:ir_function``, ``:cfg_analysis``]
  |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
  |> computeLib.add_thms [optionTheory.option_case_lazily]
fun base_ml_pause tm = let
  fun stop t = is_const t andalso List.exists
    (fn name => #Name (dest_thy_const t) = name)
    ["ml_iterate_fuel", "ml_one_pass_liveat", "ml_one_pass_used"]
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_ml_cs) tm end
(* Normalize shared inputs before the block scans duplicate their lookups. *)
fun base_ml_input i = let
  fun argument n cv = if n = 8 then RAND_CONV cv
    else RATOR_CONV (argument (n + 1) cv)
  fun normalize tm = let
    val th = computeLib.EVAL_CONV tm
  in TRANS th (Conv.QCONV entry_compact_maps (rhs (concl th))) end
in base_eval_stage (argument i normalize) "ml_iterate_fuel" end
fun base_ml_begin_conv tm = let
  fun argument i n cv = if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  val prepared = argument 0 9 computeLib.EVAL_CONV tm
  val body = rhs (concl prepared)
  val fuel = hd (snd (strip_comb body))
  val opened = if numSyntax.dest_numeral fuel = Arbnum.zero then
      REWR_CONV (cj 1 concretizeMemLocDefsTheory.ml_iterate_fuel_def) body
    else (argument 0 9 numLib.num_CONV THENC
      REWR_CONV (cj 2 concretizeMemLocDefsTheory.ml_iterate_fuel_def) THENC
      RAND_CONV base_ml_pause) body
in TRANS prepared opened end
fun base_ml_begin g =
  if entry_has_call ["ml_iterate_fuel"] (lhs (snd g)) then
    entry_eval_stage base_ml_begin_conv "ml_iterate_fuel" g
  else ALL_TAC g
fun base_ml_part name g =
  if entry_has_call [name] (lhs (snd g)) then
    base_eval_stage (fn tm => let
      val th = computeLib.WEAK_CBV_CONV base_ml_cs tm
      val (changed,_) = pairSyntax.dest_pair (rhs (concl th))
    in if aconv changed boolSyntax.T orelse aconv changed boolSyntax.F then th
       else raise Fail ("incomplete memory-liveness scan: " ^ name)
    end) name g
  else ALL_TAC g
fun base_ml_binding tm =
  if flow_call "LET" tm then let
    val (_,args) = strip_comb tm
    fun iterator t = let val h = fst (strip_comb t) in
      is_const h andalso #Name (dest_thy_const h) = "ml_iterate_fuel" end
  in case total pairSyntax.dest_prod (type_of (List.nth(args,1))) of
       SOME (flag,rest) => flag = ``:bool`` andalso
         can pairSyntax.dest_prod rest andalso can (find_term iterator) (hd args)
     | NONE => false
  end else false
fun base_ml_resume g =
  if can (find_term base_ml_binding) (lhs (snd g)) then
    flow_transform base_ml_binding base_ml_pause g
  else ALL_TAC g
fun base_ml_finish g =
  if can (find_term base_ml_binding) (lhs (snd g)) then
    raise Fail "memory-liveness result binding remains"
  else entry_ml_finish g
val base_rename_cs = entry_plan_readonly_cs [``:ir_supply``]
  |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
  |> computeLib.add_thms [optionTheory.option_case_lazily]
val base_rename_prepare = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["rename_current_blocks", "rename_current_children"]
    (RAND_CONV computeLib.EVAL_CONV))))
fun base_rename_conv tm = let
  val prepared = REFL tm
  val equations = List.map
    (fn n => cj n makeSsaCurrentDefsTheory.rename_current_blocks_def) [1,2,3]
  val unfolded = FIRST_CONV (List.map REWR_CONV equations) (rhs (concl prepared))
  fun stop t = is_const t andalso List.exists
    (fn name => #Name (dest_thy_const t) = name)
    ["rename_current_blocks", "rename_current_children",
     "rename_current_block_insts", "update_current_succ_phis"]
  val evaluated = Lib.with_flag (computeLib.stoppers,SOME stop)
    (computeLib.WEAK_CBV_CONV base_rename_cs) (rhs (concl unfolded))
in TRANS prepared (TRANS unfolded evaluated) end
val base_rename_step = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["rename_current_blocks", "rename_current_children"]
    base_rename_conv)))
fun base_rename_part name g =
  if entry_has_call [name] (lhs (snd g)) then
    base_eval_stage (computeLib.WEAK_CBV_CONV base_rename_cs) name g
  else ALL_TAC g
fun base_dfg_tick g =
  if entry_has_call ["dfg_build_insts_rev"] (lhs (snd g)) then
    entry_eval_stage (RAND_CONV computeLib.EVAL_CONV THENC
      entry_dfg_prefix (computeLib.CBV_CONV entry_dfg_compset) 2)
      "dfg_build_insts_rev" g
  else ALL_TAC g

(* Preserve the original DFT fuel while exposing its three expensive block
   operations at separate proof boundaries. *)
fun base_dft_open_conv tm = let
  val prepared = (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV) THENC
    RAND_CONV computeLib.EVAL_CONV) tm
  val body = rhs (concl prepared)
  val (_,args) = strip_comb body
  val (_,rest) = pairSyntax.dest_pair (List.nth (args,2))
  val (_,finished) = pairSyntax.dest_pair rest
  val opened = if aconv finished boolSyntax.T then
      SIMP_CONV pure_ss
        [dftDefsTheory.dft_loop_run_fuel_done, pairTheory.SND] body
    else if numSyntax.dest_numeral (List.nth(args,1)) = Arbnum.zero then
      REWR_CONV (cj 1 dftDefsTheory.dft_loop_run_fuel_def) body
    else (RATOR_CONV (RAND_CONV numLib.num_CONV) THENC
      REWR_CONV (cj 2 dftDefsTheory.dft_loop_run_fuel_def) THENC
      RATOR_CONV (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV)) THENC
      PURE_REWRITE_CONV [COND_CLAUSES]) body
in TRANS prepared opened end
fun base_dft_open g =
  if entry_has_call ["dft_loop_run_fuel"] (lhs (snd g)) then
    base_eval_stage base_dft_open_conv "dft_loop_run_fuel" g
  else ALL_TAC g
val base_dft_cs = entry_plan_readonly_cs [``:ir_function``]
  |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
  |> computeLib.add_thms [optionTheory.option_case_lazily]
fun base_dft_state_conv tm = let
  fun stop t = is_const t andalso List.exists
    (fn name => #Name (dest_thy_const t) = name)
    ["dft_loop_run_fuel", "so_analyze_block", "so_get_stack", "dft_block"]
in RAND_CONV (Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_dft_cs)) tm end
val base_dft_state = CONV_TAC (LAND_CONV (TRY_CONV
  (base_first_conv (flow_call "dft_loop_run_fuel") base_dft_state_conv)))
fun base_dft_part name g =
  if entry_has_call [name] (lhs (snd g)) then
    base_eval_stage
      (fn tm => computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm) name g
  else ALL_TAC g
val base_bool_root = FIRST_CONV (List.map REWR_CONV
  (List.concat (List.map Drule.BODY_CONJUNCTS
    [AND_CLAUSES, OR_CLAUSES, NOT_CLAUSES, REFL_CLAUSE])))
val base_admin_types =
  [``:compilation_unit``, ``:venom_context``, ``:ir_function``,
   ``:ir_supply``, ``:fn_pass_output``, ``:pipeline_output``, ``:dft_loop_state``]
val base_admin_records = base_admin_types @
  [``:instruction``, ``:basic_block``, ``:operand``, ``:fmp_info``]
val base_admin_record_consts = List.concat (List.map (fn ty =>
  TypeBase.constructors_of ty @
  List.concat (List.map (fn (_, {accessor,fupd,...}) => [accessor,fupd])
    (TypeBase.fields_of ty))) base_admin_records)
val base_admin_cs = entry_plan_readonly_cs base_admin_types
  |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
  |> computeLib.add_thms [optionTheory.option_case_lazily]
val base_metadata_theories =
  ["min", "bool", "pair", "combin", "option", "list", "string", "char",
   "num", "prim_rec", "arithmetic", "numeral", "words", "finite_map"]
fun base_metadata_constant t =
  List.exists (aconv t) base_admin_record_consts orelse
  List.exists (fn thy => #Thy (dest_thy_const t) = thy) base_metadata_theories
fun base_metadata_conv tm = let
  fun stop t = is_const t andalso not (base_metadata_constant t)
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_admin_cs) tm end
(* Metadata is demanded only along the active case/guard spine. Preserve
   deferred compiler branches and their immutable record arguments. *)
fun base_metadata_spine_conv tm = let
  fun argument i n cv = if i = n - 1 then RAND_CONV cv
    else RATOR_CONV (argument i (n - 1) cv)
  fun descend t = let
    val (h,args) = strip_comb t
    val name = if is_const h then #Name (dest_thy_const h) else ""
    val active = case (name,List.length args) of
        ("option_CASE",3) => SOME 0 | ("pair_CASE",2) => SOME 0
      | ("UNCURRY",2) => SOME 1 | ("OPTION_MAP",2) => SOME 1
      | ("COND",3) => SOME 0 | _ => NONE
  in case active of
      SOME i => argument i (List.length args) base_metadata_spine_conv t
    | NONE => if is_const h andalso base_metadata_constant h
        then base_metadata_conv t else REFL t
  end
  val th = case total (CHANGED_CONV entry_plan_root_conv) tm of
      SOME th => th | NONE => descend tm
in if aconv (lhs (concl th)) (rhs (concl th)) then th
   else TRANS th (base_metadata_spine_conv (rhs (concl th)))
end
val base_fmp_resume = CONV_TAC (LAND_CONV base_metadata_spine_conv)
fun base_bool_conv tm =
  case total (CHANGED_CONV base_bool_root) tm of
      SOME th => TRANS th (base_bool_conv (rhs (concl th)))
    | NONE => if boolSyntax.is_conj tm orelse boolSyntax.is_disj tm orelse
                 boolSyntax.is_neg tm then let
        val th = if boolSyntax.is_neg tm then RAND_CONV base_bool_conv tm
                 else BINOP_CONV base_bool_conv tm
      in if aconv (lhs (concl th)) (rhs (concl th)) then th
         else TRANS th (base_bool_conv (rhs (concl th))) end
      else let val h = fst (strip_comb tm) in
        if is_const h andalso base_metadata_constant h andalso
           List.null (free_vars tm) then Conv.QCONV base_metadata_conv tm
        else REFL tm
      end
val base_guard_check = CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["COND"]
    (RATOR_CONV (RATOR_CONV (RAND_CONV base_bool_conv))))))
val base_guard_admin = plan_admin >> base_guard_check >> plan_admin
val admin = base_guard_admin
val pass_open = flow_named "run_configured_fn_pass_fold"
  (FIRST_CONV (List.map (fn i => REWR_CONV
    (cj i venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)) [1,2]))
val current_function = entry_stage "unit_with_current_fn"
val execute = base_eval_stage
  (fn tm => computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm)
  "execute_configured_fn_pass"
val finish_pass = entry_stage "run_configured_fn_pass_fold"
val replace_function = entry_stage "replace_unique_function"
val apply_labels = entry_stage "apply_unit_label_map"
val labels_ok = entry_guard "unit_labels_wf"
val labels_preserved = entry_guard "list_subset"
val instruction_ids = entry_guard "unit_global_inst_ids_distinct"

fun base_target name g = let
  fun selected tm = let val (h,args) = strip_comb tm in
    is_const h andalso #Name (dest_thy_const h) = name andalso
    List.length args = entry_function_arity (type_of h) andalso
    List.null (free_vars tm) end
in find_term selected (lhs (snd g)) end
fun base_subset_cert g = let
  val th = entry_literal_subset_conv (base_target "list_subset" g)
  val () = if aconv (rhs (concl th)) boolSyntax.T then ()
    else raise Fail "supply subset guard is not true"
in ALL_TAC g end
fun base_stage name g = let
  val target = base_target name g
  val th = CHANGED_CONV
    (if name = "list_subset" then entry_literal_subset_conv
     else computeLib.WEAK_CBV_CONV (computeLib.the_compset())) target
in CONV_TAC (LAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV
     (fn t => if aconv t target then th else NO_CONV t)))) g end
val base_package = base_stage "package_external_fn"
val allocation_open = base_eval_stage
  (REWR_CONV concretizeMemLocDefsTheory.compute_alloc_map_fuel_in_context_def THENC
   REWR_CONV LET_THM THENC BETA_CONV THENC
   REWR_CONV LET_THM THENC BETA_CONV THENC
   REWR_CONV LET_THM THENC BETA_CONV) "compute_alloc_map_fuel_in_context"
val allocation_finish_open = simp_tac pure_ss [LET_THM]

(* Open one block without checking all its instructions at once. Subsequent
   boundaries check one instruction; the final guard folds the proved Ts. *)
fun base_dominance_conv tm = let
  val prepared = RAND_CONV computeLib.EVAL_CONV tm
  val body = rhs (concl prepared)
  val (items,element_type) = listSyntax.dest_list (rand body)
  val opened = FIRST_CONV
    [REWR_CONV (cj 1 listTheory.EVERY_DEF),
     REWR_CONV (cj 2 listTheory.EVERY_DEF)] body
  val checked = if List.null items then REFL (rhs (concl opened))
    else if element_type = ``:basic_block`` then
      LAND_CONV (TRY_CONV BETA_CONV) (rhs (concl opened))
    else LAND_CONV (fn t => let
      val th = computeLib.EVAL_CONV t
      val result = rhs (concl th)
    in if aconv result boolSyntax.T orelse aconv result boolSyntax.F then th
       else raise Fail "incomplete instruction dominance check"
    end) (rhs (concl opened))
in TRANS prepared (TRANS opened checked) end
fun base_dominance_tick g =
  if can (find_term entry_dominance_every) (lhs (snd g)) then
    flow_transform entry_dominance_every base_dominance_conv g
  else ALL_TAC g

(* Two finite planner transitions per timed boundary. The shared analysis
   records are abbreviated before replay, as in the multi-default fixture. *)
(* Normalize one changing instruction input, preserving the original order
   4..9 when the six-input boundary needs finer timing. *)
fun base_plan_input i = let
  val () = if i >= 4 andalso i <= 9 then ()
    else raise Fail "instruction input index is outside 4..9"
  fun normalize tm = let
    val evaluate = entry_plan_compute
      (computeLib.WEAK_CBV_CONV (entry_plan_instruction_cs tm))
    fun argument n cv = if n = 9 then RAND_CONV cv
      else RATOR_CONV (argument (n + 1) cv)
  in argument i evaluate tm end
in CONV_TAC (LAND_CONV (TRY_CONV
  (entry_plan_active ["generate_inst_plan"] normalize))) end

val base_plan_pair =
  plan_control >> plan_admin >> plan_block >> plan_admin >> plan_setup >>
  plan_inputs >> plan_instruction >> plan_admin >>
  plan_control >> plan_admin >> plan_block >> plan_admin >> plan_setup >>
  plan_inputs >> plan_instruction >> plan_admin

val base_ready_open = simp_tac pure_ss
  ([stackPlanGenTheory.codegen_ready_def, listTheory.EVERY_DEF, combinTheory.K_THM] @
    #rewrs (TypeBase.simpls_of ``:venom_context``) @
    #rewrs (TypeBase.simpls_of ``:compilation_unit``))
fun base_ready_named name = flow_transform
  (fn tm => if flow_call "codegen_ready_fn" tm then let
      val func = hd (snd (strip_comb tm))
       val named = computeLib.EVAL_CONV
         (mk_comb (``\(f:ir_function). f.fn_name``,func))
    in stringSyntax.fromHOLstring (rhs (concl named)) = name end
    else false)
  (fn tm => let val th = computeLib.EVAL_CONV tm
    in if aconv (rhs (concl th)) boolSyntax.T then th
       else raise Fail ("codegen readiness rejected " ^ name) end)
(* Internal labels include the function id, declared parameter types and
   deployment mode. Derive the label with the compiler API. *)
fun base_ready_internal fn_id name arg_types is_ctor = let
  val query = list_mk_comb
    (prim_mk_const {Thy="compileEnv",Name="internal_fn_label"},
     [numSyntax.term_of_int fn_id, stringSyntax.fromMLstring name, arg_types,
      if is_ctor then boolSyntax.T else boolSyntax.F])
  val label = stringSyntax.fromHOLstring
    (rhs (concl (computeLib.EVAL_CONV query)))
in base_ready_named label end
val base_ready_finish = CONV_TAC (LAND_CONV
  (entry_plan_active ["COND"] (RATOR_CONV (RATOR_CONV (RAND_CONV
    (base_boolean_conv computeLib.EVAL_CONV "codegen readiness"))))))

end

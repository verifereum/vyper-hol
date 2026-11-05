(* Kernel conversions for the existing generic dataflow worklist. Each call
   evaluates one initialization binding or one original worklist transition. *)
structure evalCompilerFlowLib = struct
open HolKernel Parse boolLib bossLib boolTheory
open evalCompilerEntryLib

fun flow_call name tm = let val (h,args) = strip_comb tm in
  is_const h andalso #Name (dest_thy_const h) = name andalso
  List.length args = entry_function_arity (type_of h) andalso
  List.null (free_vars tm)
end
fun flow_lift target th = CONV_TAC (LAND_CONV (CHANGED_CONV (ONCE_DEPTH_CONV
  (fn tm => if aconv tm target then th else NO_CONV tm))))
fun flow_transform selected evaluate g = let
  val target = find_term selected (lhs (snd g))
  val th = CHANGED_CONV evaluate target
in flow_lift target th g end
fun flow_named name evaluate = flow_transform (flow_call name) evaluate

val entry_dom_flow_open = flow_named "dom_fixpoint"
  (SIMP_CONV pure_ss [dominatorDefsTheory.dom_fixpoint_def, LET_THM])
val entry_live_flow_open = flow_named "liveness_analyze"
  (SIMP_CONV pure_ss [livenessDefsTheory.liveness_analyze_def,
    livenessDefsTheory.liveness_recompute_def])
val entry_flow_open = flow_named "df_analyze"
  (REWR_CONV dfAnalyzeDefsTheory.df_analyze_def)
fun flow_state_type tm = (fst (dest_type (type_of tm)) = "df_state")
  handle HOL_ERR _ => false
fun flow_header tm = let
  val (h,args) = strip_comb tm
  val state_type = flow_state_type tm
in is_const h andalso #Name (dest_thy_const h) = "LET" andalso
   List.length args = 2 andalso state_type andalso List.null (free_vars tm)
end
fun flow_header_conv tm = let
  val prepared = if entry_has_call ["wl_iterate"] (rand tm) then REFL tm
    else (RAND_CONV (computeLib.WEAK_CBV_CONV (computeLib.the_compset())) tm
      handle UNCHANGED => REFL tm)
  fun beta t = BETA_CONV t handle HOL_ERR _ => REFL t | UNCHANGED => REFL t
  val opened = (REWR_CONV LET_THM THENC beta) (rhs (concl prepared))
in TRANS prepared opened end
fun entry_flow_header g =
  if can (find_term flow_header) (lhs (snd g)) then
    flow_transform flow_header flow_header_conv g
  else ALL_TAC g
fun entry_flow_header_finish g =
  if can (find_term flow_header) (lhs (snd g)) then
    raise Fail "dataflow initialization needs more finite binding boundaries"
  else ALL_TAC g

(* Unfold WHILE once, evaluate its guard and only its one selected step, then
   fold the remaining WHILE back to the unchanged worklist API. *)
fun flow_step tm = let
  val opened = REWR_CONV worklistDefsTheory.wl_iterate_def tm
  val unfolded = REWR_CONV WhileTheory.WHILE (rhs (concl opened))
  val guarded = RATOR_CONV (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV))
    (rhs (concl unfolded))
  val chosen = PURE_REWRITE_CONV [COND_CLAUSES] (rhs (concl guarded))
  val body = rhs (concl chosen)
  val advanced = if pairSyntax.is_pair body then REFL body
    else let
      val step = RAND_CONV
        (computeLib.WEAK_CBV_CONV (computeLib.the_compset())) body
      val folded = REWR_CONV (GSYM worklistDefsTheory.wl_iterate_def)
        (rhs (concl step))
    in TRANS step folded end
in TRANS opened (TRANS unfolded (TRANS guarded (TRANS chosen advanced))) end
fun entry_flow_tick g =
  if entry_has_call ["wl_iterate"] (lhs (snd g)) then
    flow_named "wl_iterate" flow_step g
  else ALL_TAC g
fun entry_flow_finish g =
  if entry_has_call ["wl_iterate", "WHILE"] (lhs (snd g)) then
    raise Fail "dataflow worklist needs more finite transition boundaries"
  else ALL_TAC g
val entry_flow_populate = flow_named "df_populate_inst"
  (fn tm => computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm)
val entry_flow_state_result = flow_transform
  (fn tm => flow_call "SND" tm andalso flow_state_type tm)
  (REWR_CONV pairTheory.SND)
val entry_flow_compact = TRY (flow_transform
  (fn tm => flow_state_type tm andalso List.null (free_vars tm)) entry_compact_maps)
end

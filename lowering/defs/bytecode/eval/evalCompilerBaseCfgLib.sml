(* Original SimplifyCFG rounds, with their existing decreasing fuel retained. *)
structure evalCompilerBaseCfgLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

val base_cfg_iter_cs = entry_plan_readonly_cs
  [``:ir_function``, ``:cfg_analysis``]
val base_cfg_iter_open = base_eval_stage
  (REWR_CONV simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def)
  "simplify_cfg_fn_with_labels"
fun base_cfg_iter_pause tm = let
  fun stop t = is_const t andalso List.exists
    (fn n => #Name (dest_thy_const t) = n)
    ["simplify_cfg_iter_with_labels", "simplify_cfg_round_with_labels"]
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_cfg_iter_cs) tm end
fun base_cfg_iter_begin_conv tm = let
  val prepared = RATOR_CONV (RAND_CONV computeLib.EVAL_CONV) tm
  val body = rhs (concl prepared)
  val fuel = hd (snd (strip_comb body))
  val opened = if numSyntax.dest_numeral fuel = Arbnum.zero then
      REWR_CONV (cj 1 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def) body
    else (RATOR_CONV (RAND_CONV numLib.num_CONV) THENC
      REWR_CONV (cj 2 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def)) body
in TRANS prepared opened end
fun base_cfg_iter_begin g =
  if entry_has_call ["simplify_cfg_iter_with_labels"] (lhs (snd g)) then
    base_eval_stage base_cfg_iter_begin_conv "simplify_cfg_iter_with_labels" g
  else ALL_TAC g
fun base_cfg_round g =
  if entry_has_call ["simplify_cfg_round_with_labels"] (lhs (snd g)) then
    base_eval_stage (fn tm => let
      val th = computeLib.WEAK_CBV_CONV base_cfg_iter_cs tm
      val _ = pairSyntax.dest_pair (rhs (concl th))
    in th end) "simplify_cfg_round_with_labels" g
  else ALL_TAC g
val base_cfg_iter_resume = CONV_TAC (LAND_CONV base_cfg_iter_pause)
fun base_cfg_iter_finish g =
  if entry_has_call
      ["simplify_cfg_iter_with_labels", "simplify_cfg_round_with_labels"]
      (lhs (snd g)) then
    raise Fail "SimplifyCFG needs more original round boundaries"
  else ALL_TAC g
end

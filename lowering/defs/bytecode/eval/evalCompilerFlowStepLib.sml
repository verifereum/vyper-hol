(* Separately timed parts of one original wl_step; no extra analysis fuel. *)
structure evalCompilerFlowStepLib = struct
open HolKernel Parse boolLib bossLib boolTheory
open evalCompilerEntryLib evalCompilerFlowLib

fun flow_phase name evaluate g =
  if entry_has_call [name] (lhs (snd g)) then flow_named name evaluate g
  else ALL_TAC g

fun flow_begin tm = let
  val opened = REWR_CONV worklistDefsTheory.wl_iterate_def tm
  val unfolded = REWR_CONV WhileTheory.WHILE (rhs (concl opened))
  val guard = RATOR_CONV (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV))
    (rhs (concl unfolded))
  val chosen = PURE_REWRITE_CONV [COND_CLAUSES] (rhs (concl guard))
in TRANS opened (TRANS unfolded (TRANS guard chosen)) end
val entry_flow_begin = flow_phase "wl_iterate" flow_begin

val entry_flow_step_open = flow_phase "wl_step"
  (RAND_CONV (LAND_CONV computeLib.EVAL_CONV) THENC FIRST_CONV
    [REWR_CONV worklistStepComputeTheory.wl_step_cons,
     REWR_CONV worklistStepComputeTheory.wl_step_nil])

(* The pending transition is the last argument of WHILE. Evaluate the new
   state once while its binding still shares that result with both branches. *)
val entry_flow_transfer = flow_phase "WHILE"
  (RAND_CONV (RAND_CONV (fn tm =>
    computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm)))
val entry_flow_bind = flow_phase "WHILE"
  (RAND_CONV (REWR_CONV LET_THM THENC TRY_CONV BETA_CONV))
val entry_flow_changed = flow_phase "WHILE"
  (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV computeLib.EVAL_CONV))))
val entry_flow_select = flow_phase "WHILE"
  (RAND_CONV (FIRST_CONV (List.map REWR_CONV
    (Drule.BODY_CONJUNCTS COND_CLAUSES))))
val entry_flow_resume = flow_phase "WHILE"
  (RAND_CONV (LAND_CONV computeLib.EVAL_CONV) THENC
   REWR_CONV (GSYM worklistDefsTheory.wl_iterate_def))
end

(* Original reclaim analysis, with its independent analyses timed separately. *)
structure evalCompilerBaseReclaimLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

val base_reclaim_equation = ref (NONE : thm option)
fun base_reclaim_open g = let
  val target = find_term (flow_call "analyze_fmp_reclaims") (lhs (snd g))
  val th = REWR_CONV fmpReclaimDefsTheory.analyze_fmp_reclaims_def target
in base_reclaim_equation := SOME th; ALL_TAC g end
fun base_reclaim_update convert g = let
  val th = valOf (!base_reclaim_equation)
  val next = TRANS th (Conv.QCONV convert (rhs (concl th)))
in base_reclaim_equation := SOME next; ALL_TAC g end
val base_reclaim_select = FIRST_CONV (List.map REWR_CONV
  (Drule.BODY_CONJUNCTS COND_CLAUSES))
val base_reclaim_guard_cs = entry_plan_readonly_cs
  [``:ir_function``, ``:venom_context``, ``:fmp_info``]
val base_reclaim_guard = base_reclaim_update
  (RATOR_CONV (RATOR_CONV (RAND_CONV
     (base_boolean_conv (computeLib.CBV_CONV base_reclaim_guard_cs)
       "reclaim preconditions"))) THENC base_reclaim_select)
fun base_reclaim_named convert name = base_reclaim_update
  (base_first_conv (flow_call name) convert)
val base_reclaim_states_open = base_reclaim_named
  (REWR_CONV fmpReclaimDefsTheory.fmp_reclaim_states_def) "fmp_reclaim_states"
fun base_reclaim_measure label tac g = let
  val timer = Timer.startCPUTimer ()
  val started = Time.now ()
  fun report status = let val {usr,sys} = Timer.checkCPUTimer timer in
    print (label ^ " " ^ status ^ " wall=" ^ Time.toString (Time.-(Time.now(),started)) ^
      " cpu=" ^ Time.toString (Time.+(usr,sys)) ^
      " gc=" ^ Time.toString (Timer.checkGCTime timer) ^ "\n") end
in (let val result = tac g in report "ok"; result end)
   handle e => (report "failed"; raise e)
end
val base_reclaim_states = base_reclaim_measure "reclaim-states"
  (base_reclaim_named (computeLib.WEAK_CBV_CONV base_fmp_reclaim_cs)
    "fmp_reclaim_analyze_fuel")
(* Keep the candidate plan shared until it has been computed. *)
fun base_reclaim_resume_conv tm = let
  fun stop t = is_const t andalso
    (#Name (dest_thy_const t) = "LET" orelse not (base_metadata_constant t))
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_admin_cs) tm end
val base_reclaim_resume = base_reclaim_update base_reclaim_resume_conv
val base_reclaim_candidate_equation = ref (NONE : thm option)
fun base_reclaim_candidates_open g = let
  val body = rhs (concl (valOf (!base_reclaim_equation)))
  val query = find_term (flow_call "fmp_candidate_plan") body
  val th = REWR_CONV fmpReclaimDefsTheory.fmp_candidate_plan_def query
in base_reclaim_candidate_equation := SOME th; ALL_TAC g end
fun base_reclaim_candidate_analysis name g = let
  val th = valOf (!base_reclaim_candidate_equation)
  val next = TRANS th (base_first_conv (flow_call name)
    (computeLib.WEAK_CBV_CONV base_fmp_reclaim_cs) (rhs (concl th)))
in base_reclaim_candidate_equation := SOME next; ALL_TAC g end
val base_reclaim_candidate_live = base_reclaim_candidate_analysis "liveness_analyze"
val base_reclaim_candidate_cfg = base_reclaim_candidate_analysis "cfg_analyze"
fun base_reclaim_candidates_finish g = let
  val th = valOf (!base_reclaim_candidate_equation)
  val evaluated = computeLib.WEAK_CBV_CONV base_fmp_reclaim_cs (rhs (concl th))
  val result = rhs (concl evaluated)
  val () = if entry_has_call ["liveness_analyze", "cfg_analyze",
      "fmp_collect_candidates", "fmp_plan_of_list"] result then
      raise Fail "candidate analysis remained symbolic" else ()
  val checked = TRANS th (TRANS evaluated (Conv.QCONV entry_compact_maps result))
  val query = lhs (concl checked)
  val () = base_reclaim_candidate_equation := NONE
in base_reclaim_update (base_first_conv (aconv query) (K checked)) g end
val base_reclaim_bind = base_reclaim_update base_metadata_conv
val base_reclaim_plan_check = base_reclaim_named
  (base_boolean_conv (computeLib.CBV_CONV base_fmp_reclaim_cs)
    "reclaim plan") "fmp_reclaim_plan_ok"
fun base_reclaim_finish g = let
  val th = valOf (!base_reclaim_equation)
  val resumed = Conv.QCONV base_metadata_conv (rhs (concl th))
  val result = rhs (concl resumed)
  val () = if optionSyntax.is_some result orelse optionSyntax.is_none result
    then () else raise Fail "staged reclaim analysis remained symbolic"
  val finished = TRANS th (TRANS resumed (Conv.QCONV entry_compact_maps result))
  val target = lhs (concl finished)
  val () = base_reclaim_equation := NONE
in CONV_TAC (LAND_CONV (base_first_conv (aconv target) (K finished))) g end
end

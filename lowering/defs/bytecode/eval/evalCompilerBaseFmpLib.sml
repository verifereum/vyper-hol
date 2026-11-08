(* Exact context analysis: expose the original finite FUNPOW, then evaluate
   its seed and each original synchronous round at separate boundaries. *)
structure evalCompilerBaseFmpLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

val base_fmp_context_equation = ref (NONE : thm option)
val base_fmp_context_cs = entry_plan_readonly_cs
  [``:venom_context``, ``:ir_function``, ``:fmp_info``,
   ``:compilation_unit``, ``:fn_pass_output``, ``:ir_supply``]
fun base_fmp_context_open g = let
  val query = find_term (flow_call "analyze_fmp_context") (lhs (snd g))
  val th = REWR_CONV fmpAnalysisDefsTheory.analyze_fmp_context_def query
in base_fmp_context_equation := SOME th; ALL_TAC g end
fun base_fmp_context_update convert g = let
  val th = valOf (!base_fmp_context_equation)
  val next = TRANS th (Conv.QCONV convert (rhs (concl th)))
in base_fmp_context_equation := SOME next; ALL_TAC g end
val base_fmp_context_count = base_fmp_context_update
  (RATOR_CONV (RAND_CONV
    (computeLib.WEAK_CBV_CONV base_fmp_context_cs THENC computeLib.EVAL_CONV)))
val base_fmp_context_unroll = base_fmp_context_update (fn tm => let
  fun stop t = is_const t andalso List.exists
    (fn n => #Name (dest_thy_const t) = n)
    ["fmp_option_step", "seed_fmp_context"]
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_fmp_context_cs) tm end)
val base_fmp_context_seed = base_fmp_context_update
  (base_first_conv (flow_call "seed_fmp_context")
    (computeLib.WEAK_CBV_CONV base_fmp_context_cs))
fun base_fmp_context_ready tm =
  flow_call "fmp_option_step" tm andalso let
    val state = List.nth (snd (strip_comb tm),1)
  in optionSyntax.is_some state orelse optionSyntax.is_none state end
val base_fmp_context_step = base_fmp_context_update
  (base_first_conv base_fmp_context_ready
    (computeLib.WEAK_CBV_CONV base_fmp_context_cs))
fun base_fmp_context_finish g = let
  val th = valOf (!base_fmp_context_equation)
  val body = rhs (concl th)
  val () = if entry_has_call ["FUNPOW", "seed_fmp_context", "fmp_option_step"] body
      then raise Fail "FMP context needs more finite synchronous rounds" else ()
  val normalized = computeLib.EVAL_CONV body
  val result = rhs (concl normalized)
  val () = if optionSyntax.is_some result orelse optionSyntax.is_none result
      then () else raise Fail "FMP context analysis remained symbolic"
  val checked = TRANS th
    (TRANS normalized (Conv.QCONV entry_compact_maps result))
  val query = lhs (concl checked)
  val () = base_fmp_context_equation := NONE
in CONV_TAC (LAND_CONV (base_first_conv (aconv query) (K checked))) g end

(* Keep the seven original input obligations independently timed. *)
val base_fmp_guard_equation = ref (NONE : thm option)
fun base_fmp_guard_open g = let
  val query = find_term (flow_call "fmp_lower_input") (lhs (snd g))
  val th = REWR_CONV fmpLowerDefsTheory.fmp_lower_input_def query
in base_fmp_guard_equation := SOME th; ALL_TAC g end
fun base_fmp_guard_part i g = let
  val th = valOf (!base_fmp_guard_equation)
  val check = base_boolean_conv
    (computeLib.CBV_CONV base_fmp_context_cs) "FMP input conjunct"
  fun clause n tm =
    if boolSyntax.is_conj tm then
      (if n = 0 then LAND_CONV check else RAND_CONV (clause (n - 1))) tm
    else if n = 0 then check tm
    else raise Fail "missing FMP input conjunct"
  val next = TRANS th (clause i (rhs (concl th)))
in base_fmp_guard_equation := SOME next; ALL_TAC g end
fun base_fmp_guard_finish g = let
  val th = valOf (!base_fmp_guard_equation)
  val checked = TRANS th
    (SIMP_CONV pure_ss [boolTheory.AND_CLAUSES] (rhs (concl th)))
  val result = rhs (concl checked)
  val () = if aconv result boolSyntax.T orelse aconv result boolSyntax.F then ()
    else raise Fail "FMP input guard remained symbolic"
  val query = lhs (concl checked)
  val () = base_fmp_guard_equation := NONE
in CONV_TAC (LAND_CONV (base_first_conv (aconv query) (K checked))) g end
end

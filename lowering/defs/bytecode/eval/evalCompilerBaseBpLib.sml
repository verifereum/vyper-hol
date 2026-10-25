(* Evaluate the original bounded base-pointer analysis one synchronous pass
   at a time. No analysis fuel is introduced or discarded. *)
structure evalCompilerBaseBpLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

val base_bp_cs = entry_plan_readonly_cs [``:ir_function``, ``:cfg_analysis``]
  |> (fn cs => computeLib.set_skip cs boolSyntax.conditional (SOME 1))
  |> computeLib.add_thms [optionTheory.option_case_lazily]
fun base_bp_argument i n cv = if i = n - 1 then RAND_CONV cv
  else RATOR_CONV (base_bp_argument i (n - 1) cv)
val base_bp_open = base_eval_stage
  (REWR_CONV concretizeMemLocDefsTheory.bp_analyze_fuel_def) "bp_analyze_fuel"
val base_bp_order = base_eval_stage
  (base_bp_argument 2 4
    (computeLib.WEAK_CBV_CONV base_bp_cs THENC computeLib.EVAL_CONV))
  "bp_iterate_fuel"
fun base_bp_pause tm = let
  fun stop t = is_const t andalso List.exists
    (fn name => #Name (dest_thy_const t) = name)
    ["bp_iterate_fuel", "bp_one_pass"]
in Lib.with_flag (computeLib.stoppers,SOME stop)
     (computeLib.WEAK_CBV_CONV base_bp_cs) tm end
fun base_bp_begin_conv tm = let
  val prepared = base_bp_argument 0 4 computeLib.EVAL_CONV tm
  val body = rhs (concl prepared)
  val fuel = hd (snd (strip_comb body))
  val opened = if numSyntax.dest_numeral fuel = Arbnum.zero then
      REWR_CONV (cj 1 concretizeMemLocDefsTheory.bp_iterate_fuel_def) body
    else (base_bp_argument 0 4 numLib.num_CONV THENC
      REWR_CONV (cj 2 concretizeMemLocDefsTheory.bp_iterate_fuel_def)) body
in TRANS prepared opened end
fun base_bp_begin g =
  if entry_has_call ["bp_iterate_fuel"] (lhs (snd g)) then
    base_eval_stage base_bp_begin_conv "bp_iterate_fuel" g
  else ALL_TAC g
fun base_bp_pass g =
  if entry_has_call ["bp_one_pass"] (lhs (snd g)) then
    base_eval_stage (fn tm => let
      val timer = Timer.startCPUTimer ()
      fun report status = let val {usr,sys} = Timer.checkCPUTimer timer in
        print ("base-pointer pass " ^ status ^ " cpu=" ^
          Time.toString (Time.+(usr,sys)) ^ " gc=" ^
          Time.toString (Timer.checkGCTime timer) ^ "\n") end
      val th = (computeLib.WEAK_CBV_CONV base_bp_cs tm
        handle e => (report "failed"; raise e))
      val () = report "ok"
      val (changed,_) = pairSyntax.dest_pair (rhs (concl th))
    in if aconv changed boolSyntax.T orelse aconv changed boolSyntax.F then th
       else raise Fail "incomplete base-pointer pass"
    end) "bp_one_pass" g
  else ALL_TAC g
fun base_bp_binding tm =
  if flow_call "LET" tm then let
    val (_,args) = strip_comb tm
    fun iterator t = let val h = fst (strip_comb t) in
      is_const h andalso #Name (dest_thy_const h) = "bp_iterate_fuel" end
  in pairSyntax.is_pair (List.nth(args,1)) andalso
     can (find_term iterator) (hd args)
  end else false
fun base_bp_resume g =
  if can (find_term base_bp_binding) (lhs (snd g)) then
    CONV_TAC (LAND_CONV
      (base_first_conv base_bp_binding base_bp_pause)) g
  else ALL_TAC g
fun base_bp_finish g =
  if entry_has_call ["bp_iterate_fuel", "bp_one_pass"] (lhs (snd g)) orelse
     can (find_term base_bp_binding) (lhs (snd g)) then
    raise Fail "base-pointer analysis needs more original synchronous rounds"
  else ALL_TAC g
end

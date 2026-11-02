(* Normalize either original subset input before proving unit coverage. *)
structure evalCompilerBaseUnitLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

(* The completed schedule needs only its original empty-list equation. *)
val base_empty_pass_fold = base_eval_stage
  (REWR_CONV (cj 1 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def))
  "run_configured_fn_pass_fold"

fun base_unit_conjunct conjunct convert g = let
  val equation = valOf (!base_supply_unit_equation)
  fun clause n tm =
    if boolSyntax.is_conj tm then
      (if n = 0 then LAND_CONV convert else RAND_CONV (clause (n - 1))) tm
    else if n = 0 then convert tm
    else raise Fail "missing unit subset conjunct"
  val checked = TRANS equation (clause conjunct (rhs (concl equation)))
in base_supply_unit_equation := SOME checked; ALL_TAC g end
fun base_unit_input conjunct argument = base_unit_conjunct conjunct
  (case argument of
      0 => RATOR_CONV (RAND_CONV computeLib.EVAL_CONV)
    | 1 => RAND_CONV computeLib.EVAL_CONV
    | _ => raise Fail "unit subset argument is outside 0..1")
fun base_unit_check conjunct = base_unit_conjunct conjunct
  (base_boolean_conv (computeLib.CBV_CONV base_supply_compset)
    "unit coverage conjunct")
end

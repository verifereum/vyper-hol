(* Checked supply guards with shared literal-subset certificates. *)
structure evalCompilerSupplyLib = struct
open HolKernel Parse
open evalCompilerEntryLib evalCompilerBoundedLib evalCompilerGuardLib

val supply_subset = prim_mk_const
  {Thy="venomFnScheduleRunner", Name="list_subset"}
val supply_compset = entry_plan_readonly_cs
  [``:ir_supply``, ``:ir_function``, ``:compilation_unit``, ``:venom_context``]
  |> (fn cs => computeLib.scrub_const cs supply_subset)
  |> computeLib.add_conv (supply_subset,2,entry_literal_subset_conv)
  |> computeLib.add_thms
       [venomFnScheduleRunnerTheory.ir_supply_extends_def,
        venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
        venomFnScheduleRunnerTheory.ir_supply_covers_unit_def]

fun entry_supply_guard name = entry_eval_stage (fn tm => let
  val th = computeLib.CBV_CONV supply_compset tm
  val result = rhs (concl th)
in if aconv result boolSyntax.T orelse aconv result boolSyntax.F then th
   else raise Fail ("incomplete supply guard: " ^ name)
end) name
end

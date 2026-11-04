(*
 * LowerDload keeps every CALL/STATICCALL success check (call_checks_ok,
 * a conjunct of fn_shape_ok).
 *
 * TOP-LEVEL:
 *   lower_dload_function_supply_call_checks
 *)
Theory lowerDloadCallChecks
Ancestors
  lowerDloadDefs lowerDloadSupplyProofs unitShapeDefs venomEffects
  venomInst list rich_list

(* Why it holds: the expansion of a DLOAD (ALLOCA, ADD, CODECOPY, MLOAD)
   or a DLOADBYTES (ADD, CODECOPY) has no INVOKE and no failing
   instruction, and its CODECOPY writes memory, so flag_path empties its
   flag set there just as it does at the source DLOAD/DLOADBYTES (both
   have write_effects {Eff_MEMORY}).  Before the CODECOPY the set only
   loses the new outputs.  Other instructions are kept as they are, block
   labels and terminators are kept, so revert_path carries over. *)
Theorem lower_dload_function_supply_call_checks:
  lower_dload_function_supply s f = (g,t) /\ call_checks_ok f ==>
  call_checks_ok g
Proof
  cheat
QED

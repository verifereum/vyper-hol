(*
 * SUE against the O1 pass contract: the step part.
 *
 * The dispatched transform is sue_expand_function_supply, which keeps every
 * block label and inserts ASSIGN copies whose outputs and instruction ids
 * come from the supply.  So one run keeps the O1 function shape, its new
 * ids are fresh against the supply it was given, its label map is empty,
 * the supply it returns still has its used ids below its next one, and it
 * adds no ALLOCA (o1_fn_row).
 *)
Theory o1ContractSueStep
Ancestors
  o1PassContract singleUseExpansionSupplyProofs singleUseExpansionDefs
  venomPassDispatcher venomWf

Theorem sue_step_contract:
  o1_step_contract_at 6 rpolicy (CFP_Simple VP_SingleUseExpansion)
Proof
  cheat
QED

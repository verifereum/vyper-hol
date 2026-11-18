(* Exhaustive opcode coverage and the resulting full-step simulation. *)
Theory stackBoundRuntime
Ancestors
  stackBoundControl stackBoundScalar stackBoundEffects stackBoundCalls
  stackBoundCreates stackBoundTerminal stackBoundStepLift

Theorem sb_all_opcode_contracts:
  !op. sb_opcode_contract op
Proof
  Cases >>
  simp[sb_stack_control_contracts, sb_scalar_contracts, sb_effect_contracts,
       sb_call_contracts, sb_create_contracts, sb_terminal_contracts]
QED

Theorem sb_step_simulates_thm:
  sb_step_simulates
Proof
  irule sb_opcode_contracts_step_simulates >>
  ACCEPT_TAC sb_all_opcode_contracts
QED

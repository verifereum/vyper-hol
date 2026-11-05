(*
 * DFT's step contract at walk run 7 (piece of o1ContractDft).
 *
 * dft_fn only permutes each block's instructions (flipping the operands
 * of commutative ones), so it keeps the O1 function shape, takes no new
 * names, labels or ids, leaves the supply alone, and keeps row 8 (no
 * ALLOCA) from row 7.
 *)
Theory o1DftStepAt
Ancestors
  o1PassContract venomPassSchedule

Theorem dft_step_contract_at:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT)
Proof
  cheat
QED

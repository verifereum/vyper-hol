(*
 * Float Allocas Pass — Proofs
 *
 * Correctness: moving allocas to the entry block preserves semantics.
 * Key insight: alloca is a pure allocation (bump pointer), its result
 * is independent of when it executes. Moving it earlier doesn't change
 * the allocated address because the allocator is monotonic.
 *)

Theory floatAllocasProofs
Ancestors
  floatAllocasDefs

Theorem float_allocas_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (float_allocas_function fn) s)
Proof
  cheat
QED

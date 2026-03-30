Theory mem2varProofs
Ancestors
  mem2varDefs basePtrProps allocaSafety

(* mem2var replaces MLOAD/MSTORE with variable operations for
 * promotable allocas. Correctness depends on:
 * - bp_ptrs_bounded: aliasing precision for determining which
 *   allocas are promotable (all accesses known, no aliases)
 * - alloca_safe_fn: mem2var makes allocas dead; if remove_unused
 *   later removes them, alloca layout changes. Non-escape ensures
 *   this doesn't affect observable output. *)
Theorem m2v_transform_function_correct_proof:
  !fuel ctx fn s bp.
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp s /\
    alloca_safe_fn fn ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (m2v_transform_function fn) s)
Proof
  cheat
QED

(* Named source invariant keeps recursive congruence premises atomic. *)
Theory selfCodeFreeInvariant
Ancestors
  selfCodeFreeContext vyperContext e2eProducers

Definition self_code_free_context_def:
  self_code_free_context cx <=>
    (!sid ts. get_module_code cx sid = SOME ts ==> ~program_reads_self_code ts)
End

Theorem self_code_free_context_stk[simp]:
  self_code_free_context (cx with stk := stk) = self_code_free_context cx
Proof simp[self_code_free_context_def, get_module_code_def]
QED

Theorem self_code_free_context_txn_code[simp]:
  self_code_free_context (cx with txn := (cx.txn with code := c)) =
  self_code_free_context cx
Proof simp[self_code_free_context_def]
QED

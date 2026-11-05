Theory exprPtrUnwrapInputFacts
Ancestors
  ptrDiscipline

(* gas_summary_ptr_at fixes the pointer-check lower bound at zero. The
   cx_tops argument of gas_outcome_ptr is only for exemption certificates. *)
Theorem unwrap_allocas_from_zero:
  allocas_from 0 s
Proof
  simp[allocas_from_def]
QED

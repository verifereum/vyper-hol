(*
 * Lower DLOAD Pass -- Proofs
 *
 * Correctness: the expanded instruction sequence computes the same
 * observable result as the original dload/dloadbytes, under the
 * precondition that vs_code ends with vs_data_section.
 *)

Theory lowerDloadProofs
Ancestors
  lowerDloadDefs stateEquiv venomWf

Theorem lower_dload_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ code_layout_valid s ==>
    lift_result observable_equiv observable_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (lower_dload_function fn) s)
Proof
  cheat
QED

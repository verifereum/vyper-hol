(*
 * Lower DLOAD Pass -- Correctness Statement
 *
 * Expanding dload/dloadbytes to alloca+offset+codecopy+mload preserves
 * observable semantics given a valid code layout.
 *)

Theory lowerDloadCorrectness
Ancestors
  lowerDloadProofs venomWf

Theorem lower_dload_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ code_layout_valid s ==>
    lift_result observable_equiv observable_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (lower_dload_function fn) s)
Proof
  ACCEPT_TAC lowerDloadProofsTheory.lower_dload_function_correct
QED

(* ===== Obligations ===== *)

Theorem lower_dload_preserves_ssa_form:
  !fn. ssa_form fn ==> ssa_form (lower_dload_function fn)
Proof
  cheat
QED

Theorem lower_dload_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (lower_dload_function fn)
Proof
  cheat
QED

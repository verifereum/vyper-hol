(* DFT pass — public API *)
Theory venomDft
Ancestors
  dftDefs dftCorrectness

(* ===== Pass-level correctness ===== *)

Theorem dft_pass_correct:
  !fn ctx s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    pass_correct (state_equiv {}) (execution_equiv {}) revert_equiv
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (dft_fn fn) s)
Proof
  ACCEPT_TAC dftCorrectnessFinalTheory.dft_pass_correct
QED

(* ===== Function-level results ===== *)

Theorem dft_fn_run_function_lift:
  !fuel ctx fn s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dft_fn fn) s)
Proof
  ACCEPT_TAC dftCorrectnessFinalTheory.dft_fn_run_function_lift
QED

Theorem dft_fn_pseudos_prefix:
  !fn. fn_pseudos_prefix fn ==> fn_pseudos_prefix (dft_fn fn)
Proof
  ACCEPT_TAC dftCorrectnessFinalTheory.dft_fn_pseudos_prefix
QED

Theorem dft_fn_entry_label:
  !fn. fn_entry_label (dft_fn fn) = fn_entry_label fn
Proof
  ACCEPT_TAC dftCorrectnessFinalTheory.dft_fn_entry_label
QED

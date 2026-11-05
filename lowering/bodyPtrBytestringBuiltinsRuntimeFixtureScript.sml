Theory bodyPtrBytestringBuiltinsRuntimeFixture
Ancestors
  bodyPtrPreds compileVyper venomCompilerTypes

(* Concrete policy witness for the empty-program counterexample frame. *)
Definition zero_probe_policy_def:
  zero_probe_policy = <|rpol_target := K T;
    rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize|>
End

Theorem zero_probe_runtime_exists:
  IS_SOME (lower_vyper_runtime_unit [] zero_probe_policy)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

(* Shared closed witnesses, kept named to avoid repeating large records. *)
Definition zero_probe_unit_def:
  zero_probe_unit = THE (lower_vyper_runtime_unit [] zero_probe_policy)
End

Definition zero_probe_cenv_def:
  zero_probe_cenv = build_compile_env [] External Nonpayable "" [] NoneT [] F
End

Definition zero_probe_cx_def:
  zero_probe_cx = empty_evaluation_context with
    <|sources := [(0w, [(NONE, [])])]; layouts := [(0w, ([], []))];
      txn := (empty_call_txn with <|block_number := 1; block_hashes := [0w]|>)|>
End

Theorem zero_probe_runtime_unit:
  lower_vyper_runtime_unit [] zero_probe_policy = SOME zero_probe_unit
Proof
  mp_tac zero_probe_runtime_exists >>
  Cases_on `lower_vyper_runtime_unit [] zero_probe_policy` >>
  simp[zero_probe_unit_def]
QED

Theorem zero_probe_no_dalloca:
  ~ctx_has_dalloca zero_probe_unit.cu_context
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem zero_probe_body_inv:
  body_inv [] zero_probe_unit.cu_context zero_probe_cenv zero_probe_cx
Proof
  rewrite_tac[bodySimTheory.body_inv_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (qexistsl_tac [`zero_probe_policy`, `zero_probe_unit`] >>
      simp[zero_probe_cx_def, vyperContextTheory.empty_evaluation_context_def,
           zero_probe_runtime_unit] >>
      EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

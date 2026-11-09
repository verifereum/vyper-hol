Theory bodyPtrBopInLiveSourceFrame
Ancestors
  bodyPtrBopInSourceFrame bodyPtrBopInEvidenceTyping bodySim vyperTypeInitialState
  venomCompilerTypes words vyperState vyperContext compileVyper supportedProgram compileEnv

(* This finite witness differs only in transaction block fields.  Keeping a
   separate transparent constant preserves the zero-block diagnostic. *)
Definition probe_live_cx_def:
  probe_live_cx = probe_cx with txn :=
    (probe_cx.txn with <| block_number := 1; block_hashes := [0w] |>)
End

Theorem live_tx_env_ok:
  tx_env_ok probe_live_cx.txn
Proof
  simp[tx_env_ok_def, probe_live_cx_def]
QED

Theorem live_body_frame:
  body_inv [] (THE (lower_vyper_runtime_unit [] probe_policy)).cu_context
    probe_cenv probe_live_cx
Proof
  simp[body_inv_def, probe_cenv_def, probe_live_cx_def, probe_cx_def,
       empty_evaluation_context_def,
       get_module_code_def, get_tenv_def, build_compile_env_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (qexistsl [`probe_policy`, `THE (lower_vyper_runtime_unit [] probe_policy)`] >>
    mp_tac empty_runtime_lowers >> Cases_on `lower_vyper_runtime_unit [] probe_policy` >>
    simp[probe_policy_def] >> EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

Theorem live_source_invariant:
  expr_sim_inv probe_cenv probe_live_cx probe_env probe_es
Proof
  simp[probe_live_cx_def, block_fields_source_invariant]
QED

Theorem live_membership_body_pre:
  expr_body_pre probe_cenv probe_live_cx probe_env probe_expr probe_es
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, live_source_invariant,
       probe_expr_def, string_membership_expression_typing_probe] >>
  EVAL_TAC >> simp[dimword_def, venomMemPropsTheory.dimindex_256] >>
  qexists `[]` >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  once_rewrite_tac[relationTheory.TC_CASES1] >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem live_membership_whole_source:
  bind (eval_expr probe_live_cx probe_expr) (read_result probe_live_cx) probe_es =
    (INL (BoolV T), probe_es)
Proof
  simp[probe_expr_def, vyperInterpreterTheory.evaluate_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.read_result_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def, vyperContextTheory.builtin_args_length_ok_def,
       vyperValueTheory.compatible_bound_def,
       vyperValueOperationTheory.evaluate_literal_def,
       vyperStateTheory.lift_sum_def, vyperASTTheory.expr_type_def,
       probe_make_array_builtin, probe_in_builtin]
QED

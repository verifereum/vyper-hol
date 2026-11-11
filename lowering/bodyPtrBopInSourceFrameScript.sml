(* Transparent constants package only this finite counterexample frame. *)
Theory bodyPtrBopInSourceFrame
Ancestors
  bodyPtrBopInEvidenceTyping bodySim vyperTypeInitialState venomCompilerTypes words vyperState vyperContext compileVyper supportedProgram

Definition probe_policy_def:
  probe_policy = <| rpol_target := all_capabilities;
                   rpol_frontend_dispatch := Linear;
                   rpol_final_assembly := FAP_Optimize |>
End

Theorem empty_runtime_lowers:
  IS_SOME (lower_vyper_runtime_unit [] probe_policy)
Proof
  EVAL_TAC >> simp[dimword_def, venomMemPropsTheory.dimindex_256]
QED

Definition probe_cenv_def:
  probe_cenv = build_compile_env [] External View "probe" [] NoneT [] F
End

Definition probe_cx_def:
  probe_cx = empty_evaluation_context with
    <| sources := [(empty_evaluation_context.txn.target, [(NONE, [])])];
       stk := [(NONE, "probe")] |>
End

Theorem empty_body_frame:
  body_inv [] (THE (lower_vyper_runtime_unit [] probe_policy)).cu_context
    probe_cenv probe_cx
Proof
  simp[body_inv_def, probe_cenv_def, probe_cx_def, empty_evaluation_context_def,
       get_module_code_def, get_tenv_def, build_compile_env_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (qexistsl [`probe_policy`, `THE (lower_vyper_runtime_unit [] probe_policy)`] >>
    mp_tac empty_runtime_lowers >> Cases_on `lower_vyper_runtime_unit [] probe_policy` >>
    simp[probe_policy_def] >> EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

Definition probe_env_def:
  probe_env = <| current_src := NONE; var_types := FEMPTY;
    var_assignable := FEMPTY; bare_globals := FEMPTY;
    bare_global_assignable := FEMPTY; toplevel_vtypes := FEMPTY;
    type_defs := FEMPTY; fn_sigs := FEMPTY;
    flag_members := FEMPTY; event_fields := FEMPTY |>
End

Definition probe_es_def:
  probe_es = initial_state initial_machine_state [FEMPTY] with outcomes := SOME []
End

Theorem block_fields_source_invariant:
  !n hs. n < 2 ** 256 ==>
    expr_sim_inv probe_cenv
      (probe_cx with txn :=
        (probe_cx.txn with <| block_number := n; block_hashes := hs |>))
      probe_env probe_es
Proof
  rpt gen_tac >> strip_tac >>
  rw[exprSimHypsDefsTheory.expr_sim_inv_def, probe_env_def, probe_es_def,
       probe_cx_def, probe_cenv_def, build_compile_env_def,
       empty_evaluation_context_def, get_tenv_def, get_module_code_def] >>
  simp[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def,
       vyperTypeInvariantsTheory.env_scopes_consistent_def,
       vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
  simp[get_tenv_def, get_module_code_def, type_env_all_modules_def,
       type_env_for_module_def, current_module_def,
       vyperTypeInvariantsTheory.fn_sigs_consistent_def,
       vyperTypeInvariantsTheory.fn_sigs_live_def,
       vyperTypeInvariantsTheory.fn_sigs_declared_complete_def,
       vyperTypeInvariantsTheory.toplevel_vtypes_complete_def,
       vyperTypeInvariantsTheory.bare_globals_complete_def,
       vyperTypeInvariantsTheory.bare_global_assignable_complete_def,
       vyperTypeInvariantsTheory.flag_members_complete_def,
       vyperTypeInvariantsTheory.context_well_typed_def,
       vyperTypeInvariantsTheory.functions_well_typed_def,
       empty_call_txn_def] >>
  rpt conj_tac >>
  gvs[AllCaseEqs(), vyperStateTheory.lookup_flag_def,
       vyperInterpreterTheory.lookup_function_def,
       vyperInterpreterTheory.lookup_callable_function_def] >>
  simp[vyperInterpreterTheory.initial_state_def,
       vyperInterpreterTheory.initial_machine_state_def, lookup_scopes_def,
       vyperTypeInvariantsTheory.state_well_typed_def,
       vyperTypeInvariantsTheory.scope_well_typed_def,
       vyperTypeInvariantsTheory.imms_well_typed_def,
       vyperTypeInvariantsTheory.accounts_well_typed_def,
       vyperTypeInvariantsTheory.account_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def] >>
  gvs[type_env_all_modules_def, type_env_for_module_def, type_env_def,
      build_flag_info_def, allocate_args_def] >>
  rpt (pop_assum mp_tac) >> EVAL_TAC >>
  simp[find_var_decl_by_name_def, AllCaseEqs()]
QED


Theorem empty_source_invariant:
  expr_sim_inv probe_cenv probe_cx probe_env probe_es
Proof
  mp_tac (Q.SPECL [`0`, `[]`] block_fields_source_invariant) >>
  simp[probe_cx_def, empty_evaluation_context_def, empty_call_txn_def]
QED

(* A shared name keeps the whole-expression certificates readable. *)
Definition probe_expr_def:
  probe_expr = Builtin (BaseT BoolT) (Bop In)
    [Literal (BaseT (UintT 256)) (IntL 1);
     Builtin (ArrayT (BaseT (UintT 256)) (Fixed 1))
       (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1))
       [Literal (BaseT (UintT 256)) (IntL 1)]]
End

Theorem membership_body_pre:
  expr_body_pre probe_cenv probe_cx probe_env probe_expr probe_es
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, empty_source_invariant,
       probe_expr_def, word_membership_expression_typing_probe] >>
  EVAL_TAC >> simp[dimword_def, venomMemPropsTheory.dimindex_256] >>
  qexists `[]` >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  once_rewrite_tac[relationTheory.TC_CASES1] >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED


Theorem probe_make_array_builtin:
  evaluate_builtin cx acc (ArrayT (BaseT (UintT 256)) (Fixed 1))
    (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1)) tys [IntV 1] =
    INL (ArrayV (SArrayV [(0,IntV 1)]))
Proof
  simp[evaluate_builtin_def] >> EVAL_TAC >>
  simp[dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC
QED

Theorem probe_in_builtin:
  evaluate_builtin cx acc (BaseT BoolT) (Bop In)
    [BaseT (UintT 256); ArrayT (BaseT (UintT 256)) (Fixed 1)]
    [IntV 1; ArrayV (SArrayV [(0,IntV 1)])] = INL (BoolV T)
Proof
  simp[evaluate_builtin_def] >> EVAL_TAC >>
  simp[dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC
QED

Theorem probe_membership_type:
  evaluate_type tenv (ArrayT (BaseT (UintT 256)) (Fixed 1)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
Proof
  EVAL_TAC >> simp[dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem membership_whole_source:
  bind (eval_expr probe_cx probe_expr) (read_result probe_cx) probe_es =
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
       probe_make_array_builtin, probe_membership_type,
       vyperStateTheory.lift_option_type_def,
       vyperValueOperationTheory.evaluate_membership_def,
       vyperValueOperationTheory.evaluate_in_array_def]
QED

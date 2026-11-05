(* Transparent constants package only this finite counterexample frame. *)
Theory bodyPtrBopInSourceFrame
Ancestors
  bodyPtrBopInProbe bodySim vyperTypeInitialState venomCompilerTypes words vyperState vyperContext compileVyper supportedProgram

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

Theorem empty_source_invariant:
  expr_sim_inv probe_cenv probe_cx probe_env probe_es
Proof
  rw[exprSimHypsDefsTheory.expr_sim_inv_def, probe_env_def, probe_es_def,
       probe_cx_def, probe_cenv_def, build_compile_env_def,
       empty_evaluation_context_def, get_tenv_def, get_module_code_def] >>
  EVAL_TAC >>
  gvs[AllCaseEqs(), vyperStateTheory.lookup_flag_def,
       vyperInterpreterTheory.lookup_function_def] >>
  rpt (pop_assum mp_tac) >> EVAL_TAC >> simp[]
QED


(* A shared name keeps the whole-expression certificates readable. *)
Definition probe_expr_def:
  probe_expr = Builtin (BaseT BoolT) (Bop In)
    [Literal (BaseT (StringT 1)) (StringL "a");
     Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
       (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
       [Literal (BaseT (StringT 1)) (StringL "a")]]
End

Theorem membership_body_pre:
  expr_body_pre probe_cenv probe_cx probe_env probe_expr probe_es
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, empty_source_invariant,
       probe_expr_def, string_membership_expression_typing_probe] >>
  EVAL_TAC >> simp[dimword_def, venomMemPropsTheory.dimindex_256] >>
  qexists `[]` >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  once_rewrite_tac[relationTheory.TC_CASES1] >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED


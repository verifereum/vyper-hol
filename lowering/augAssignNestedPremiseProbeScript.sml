(* Frozen-premise audit for the nested replacement candidate. *)
Theory augAssignNestedPremiseProbe
Ancestors
  augAssignNestedCompileProbe augAssignNestedReachProbe bodySim vyperTypeInvariants
  vyperTypeSystem vyperTypeContract vyperTypeContractFunction vyperInterpreter
  vyperContext
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_diagnostic_env_excluded:
  ~env_context_consistent nested_reach_env cx
Proof
  simp[env_context_consistent_def, nested_reach_env_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Definition nested_premise_env_def:
  nested_premise_env = nested_reach_env with
    <|bare_global_assignable := FEMPTY;
      toplevel_vtypes := FEMPTY |+ ((NONE,"a"), Type nested_reach_outer_ty)|>
End

Theorem nested_premise_typing:
  type_stmt nested_premise_env NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) = SOME nested_premise_env /\
  type_stmts nested_premise_env (BaseT (UintT 256)) nested_reach_body =
    SOME nested_premise_env
Proof
  EVAL_TAC >> simp[subscript_vtype_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def]
QED

Theorem nested_premise_context:
  env_context_consistent nested_premise_env nested_reach_cx
Proof
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[]
QED

Theorem nested_premise_supported_program:
  supported_program nested_reach_tops
Proof
  EVAL_TAC
QED

Definition nested_premise_policy_def:
  nested_premise_policy = <|rpol_target := K T;
    rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize|>
End

Theorem nested_premise_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit nested_reach_tops nested_premise_policy)
Proof
  simp[compileVyperTheory.lower_vyper_runtime_unit_def,
       nested_reach_tops_def] >> EVAL_TAC
QED

Definition nested_premise_unit_def:
  nested_premise_unit = THE
    (lower_vyper_runtime_unit nested_reach_tops nested_premise_policy)
End

Definition nested_premise_cenv_def:
  nested_premise_cenv = nested_compile_env with ce_target := K T
End

Theorem nested_premise_body_inv:
  body_inv nested_reach_tops nested_premise_unit.cu_context
    nested_premise_cenv nested_reach_cx
Proof
  rewrite_tac[body_inv_def] >>
  conj_tac >- ACCEPT_TAC nested_premise_supported_program >>
  conj_tac
  >- (qexistsl [`nested_premise_policy`, `nested_premise_unit`] >>
      simp[nested_premise_cenv_def, nested_premise_unit_def] >>
      mp_tac nested_premise_lowering_exists >>
      Cases_on `lower_vyper_runtime_unit nested_reach_tops nested_premise_policy` >>
      simp[] >> EVAL_TAC) >>
  simp[nested_premise_cenv_def, nested_compile_env_def,
       compileVyperTheory.build_compile_env_def, cenv_module_pins_def] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem nested_diagnostic_state_excluded:
  ~expr_sim_inv cenv cx env nested_reach_es
Proof
  simp[exprSimHypsDefsTheory.expr_sim_inv_def] >> EVAL_TAC
QED

Definition nested_premise_es_def:
  nested_premise_es = nested_reach_es with <|outcomes := SOME []; scopes := [FEMPTY]|>
End

Theorem nested_premise_initial_basic:
  env_consistent nested_premise_env nested_reach_cx nested_premise_es /\
  state_well_typed nested_premise_es /\
  accounts_well_typed nested_premise_es.accounts /\
  context_well_typed nested_reach_cx
Proof
  conj_tac >- (simp[env_consistent_def, nested_premise_context] >> EVAL_TAC >>
      simp[vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> gen_tac >> Cases_on `addr = 0w` >> simp[]) >>
  EVAL_TAC >> simp[]
QED

Theorem nested_premise_contract_checked:
  IS_SOME (check_contract F nested_reach_cx.layouts 0w
    [(NONE,nested_reach_tops)])
Proof
  EVAL_TAC >> simp[subscript_vtype_def,
    SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >> EVAL_TAC
QED


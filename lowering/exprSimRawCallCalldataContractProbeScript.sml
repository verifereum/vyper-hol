Theory exprSimRawCallCalldataContractProbe
Ancestors
  exprSimHyps supportedExprTraverse vyperTypeSystem compileEnv allocLimits
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST vyperContext
  vyperTypeInvariants vyperTypeCallGraphSoundness relation vyperState
  vyperCallOutcome vyperRuntimeAccounts

(* This isolates the expression-side obstruction; it does not assume
   that expr_sim_inv has an inhabitant. *)
Theorem nonreverting_calldata_admissible[local]:
  !cenv cx env es flags.
    expr_sim_inv cenv cx env es /\ call_evaluation_safe cx [] /\
    flags.rcf_revert_on_failure = F /\
    flags.rcf_is_delegate = F /\ flags.rcf_max_outsize = 0 /\
    flags.rcf_kws = [] ==>
    expr_body_pre cenv cx env
      (Call (BaseT BoolT) (RawCallCalldataTarget flags)
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w))] NONE) es
Proof
  rpt strip_tac >>
  simp[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
       raw_call_return_type_def, raw_call_kws_ok_def,
       byte_widths_expr_def, type_bits_def, alloc_limits_expr_def,
       expr_has_evm_run_def, supported_expr_exists_def,
       expr_evm_run_root_def, int_calls_expr_def,
       well_formed_type_def, expr_type_def, type_alloc_ok_def,
       is_word_type_def, type_memory_bytes_def, literal_alloc_ok_def] >> EVAL_TAC
QED

Definition probe_cx_def:
  probe_cx = empty_evaluation_context with stk := [(NONE, "")]
End

Theorem probe_module[local]:
  !src. get_module_code probe_cx src = NONE
Proof
  simp[probe_cx_def, get_module_code_def, empty_evaluation_context_def]
QED

Theorem probe_tenv[local]:
  get_tenv probe_cx = FEMPTY
Proof
  simp[probe_cx_def, get_tenv_def, empty_evaluation_context_def]
QED

Theorem probe_context_typed[local]:
  context_well_typed probe_cx
Proof
  simp[context_well_typed_def, probe_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

Theorem probe_functions_typed[local]:
  functions_well_typed probe_cx
Proof
  simp[functions_well_typed_def, probe_module]
QED

Theorem probe_call_safe[local]:
  call_evaluation_safe probe_cx []
Proof
  rewrite_tac[call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE, "")`, `[]`] >>
  simp[probe_cx_def, empty_evaluation_context_def,
       call_stack_follows_def, functions_follow_call_graph_def,
       get_module_code_def, calls_follow_call_graph_def, call_edge_rel_def] >>
  `!x y : num option # identifier. TC (call_edge_rel []) x y ==> F` by
    (ho_match_mp_tac TC_INDUCT >> simp[call_edge_rel_def]) >>
  rw[irreflexive_def] >> metis_tac[]
QED

Definition probe_env_def:
  probe_env env = env with <|current_src := NONE;
    var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY; flag_members := FEMPTY|>
End

Definition probe_es_def:
  probe_es = empty_state with <|scopes := [FEMPTY]; outcomes := SOME []|>
End

Theorem probe_env_context[local]:
  env_context_consistent (probe_env env) probe_cx
Proof
  simp[env_context_consistent_def, probe_env_def, probe_tenv,
       probe_cx_def, empty_evaluation_context_def, current_module_def,
       fn_sigs_consistent_def, fn_sigs_live_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       get_module_code_def]
QED

Theorem probe_env_scopes[local]:
  env_scopes_consistent (probe_env env) probe_cx probe_es
Proof
  simp[env_scopes_consistent_def, probe_env_def, probe_es_def,
       lookup_scopes_def]
QED

Theorem probe_env_immutables[local]:
  env_immutables_consistent (probe_env env) probe_cx probe_es
Proof
  simp[env_immutables_consistent_def, probe_env_def]
QED

Theorem probe_env_consistent[local]:
  env_consistent (probe_env env) probe_cx probe_es
Proof
  simp[env_consistent_def, probe_env_context, probe_env_scopes,
       probe_env_immutables]
QED

Theorem probe_state_typed[local]:
  state_well_typed probe_es
Proof
  simp[state_well_typed_def, probe_es_def, empty_state_def,
       scope_well_typed_def]
QED

Theorem probe_outcomes_typed[local]:
  outcomes_accounts_typed probe_es.outcomes
Proof
  simp[outcomes_accounts_typed_def, probe_es_def]
QED

Theorem probe_accounts_typed[local]:
  accounts_well_typed probe_es.accounts
Proof
  rewrite_tac[accounts_well_typed_def] >> gen_tac >>
  simp[probe_es_def, empty_state_def, account_well_typed_def] >> EVAL_TAC
QED

(* Runtime ABI bounds failures must not become source TypeErrors, including
   under every premise of main evaluator soundness. Invalid projections remain
   TypeErrors; array capacity and actual dynamic length are runtime checks. *)
Theory vyperAbiBoundsTypingTest
Ancestors
  list finite_map relation vyperAST vyperContext vyperState vyperInterpreter
  vyperAbiOperand vyperAbiAliasTest vyperTypeSystem vyperTypeInvariants
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeCallStackSoundness
  vyperTyping vyperValue
Libs
  wordsLib intLib

Definition abi_bounds_context_def:
  abi_bounds_context = empty_evaluation_context with stk := [(NONE,"main")]
End

Definition abi_bounds_env_def:
  abi_bounds_env = <|
    current_src := NONE;
    var_types := FEMPTY |+ ("a",alias_array_type);
    var_assignable := FEMPTY |+ ("a",T);
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Definition abi_bounds_expr_def:
  abi_bounds_expr = Subscript (BaseT BoolT) (Name alias_array_type "a")
    (Literal (BaseT (UintT 256)) (IntL 2))
End

Theorem abi_bounds_expr_well_typed:
  well_typed_expr abi_bounds_env abi_bounds_expr
Proof
  EVAL_TAC
QED

Theorem abi_bounds_expr_raises_runtime_error:
  FST (eval_abi_expr abi_bounds_context abi_bounds_expr alias_state) =
    INR (Error (RuntimeError "ABI subscript bounds"))
Proof
  EVAL_TAC
QED

Definition abi_bounds_encode_def:
  abi_bounds_encode = TypeBuiltin (BaseT (BytesT (Dynamic 32)))
    (AbiEncode F NONE) (TupleT [BaseT BoolT]) [abi_bounds_expr]
End

Theorem abi_bounds_encode_well_typed:
  well_typed_expr abi_bounds_env abi_bounds_encode
Proof
  EVAL_TAC >> simp[]
QED

Theorem abi_bounds_encode_raises_runtime_error:
  FST (eval_expr abi_bounds_context abi_bounds_encode alias_state) =
    INR (Error (RuntimeError "ABI subscript bounds"))
Proof
  EVAL_TAC
QED

Theorem abi_bounds_initial_state_well_typed:
  state_well_typed alias_state
Proof
  EVAL_TAC >> rw[value_has_type_def, well_formed_type_value_def, type_slot_size_def]
QED

Theorem abi_bounds_calls_safe:
  call_evaluation_safe abi_bounds_context (int_calls_expr abi_bounds_encode)
Proof
  rewrite_tac[call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"main")`, `[]`] >>
  simp[abi_bounds_context_def, empty_evaluation_context_def,
       abi_bounds_encode_def, abi_bounds_expr_def, int_calls_expr_def,
       call_stack_follows_def, functions_follow_call_graph_def,
       calls_follow_call_graph_def, get_module_code_def,
       irreflexive_def, Once TC_CASES1, call_edge_rel_def]
QED

Theorem abi_bounds_context_preconditions:
  context_well_typed abi_bounds_context /\
  functions_well_typed abi_bounds_context /\
  accounts_well_typed alias_state.accounts /\
  call_evaluation_safe abi_bounds_context (int_calls_expr abi_bounds_encode)
Proof
  rpt conj_tac >| [EVAL_TAC, EVAL_TAC >> simp[], EVAL_TAC >> simp[],
                  ACCEPT_TAC abi_bounds_calls_safe]
QED

Theorem abi_bounds_env_consistent:
  env_consistent abi_bounds_env abi_bounds_context alias_state
Proof
  EVAL_TAC >> rw[] >> EVAL_TAC
QED

Theorem abi_bounds_main_soundness_runtime_error:
  well_typed_expr abi_bounds_env abi_bounds_encode /\
  env_consistent abi_bounds_env abi_bounds_context alias_state /\
  state_well_typed alias_state /\
  context_well_typed abi_bounds_context /\
  functions_well_typed abi_bounds_context /\
  accounts_well_typed alias_state.accounts /\
  call_evaluation_safe abi_bounds_context (int_calls_expr abi_bounds_encode) /\
  FST (eval_expr abi_bounds_context abi_bounds_encode alias_state) =
    INR (Error (RuntimeError "ABI subscript bounds")) /\
  (!msg. FST (eval_expr abi_bounds_context abi_bounds_encode alias_state) <>
    INR (Error (TypeError msg)))
Proof
  simp[abi_bounds_encode_well_typed, abi_bounds_env_consistent,
       abi_bounds_initial_state_well_typed, abi_bounds_context_preconditions,
       abi_bounds_encode_raises_runtime_error]
QED

(* General all-index no-TypeError projection lemmas are exported directly by
   vyperAbiOperand, so the main typing proof can use them without test imports. *)

(* An in-bounds expression satisfies the same complete soundness premises. *)
Definition abi_good_expr_def:
  abi_good_expr = Subscript (BaseT BoolT) (Name alias_array_type "a")
    (Literal (BaseT (UintT 256)) (IntL 0))
End

Definition abi_good_encode_def:
  abi_good_encode = TypeBuiltin (BaseT (BytesT (Dynamic 32)))
    (AbiEncode F NONE) (TupleT [BaseT BoolT]) [abi_good_expr]
End

Theorem abi_good_calls_safe:
  call_evaluation_safe abi_bounds_context (int_calls_expr abi_good_encode)
Proof
  rewrite_tac[call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"main")`, `[]`] >>
  simp[abi_bounds_context_def, empty_evaluation_context_def,
       abi_good_encode_def, abi_good_expr_def, int_calls_expr_def,
       call_stack_follows_def, functions_follow_call_graph_def,
       calls_follow_call_graph_def, get_module_code_def,
       irreflexive_def, Once TC_CASES1, call_edge_rel_def]
QED

Theorem abi_good_encode_result:
  FST (eval_expr abi_bounds_context abi_good_encode alias_state) =
    INL (Value (BytesV (REPLICATE 31 0w ++ [1w])))
Proof
  EVAL_TAC
QED

Theorem abi_good_main_soundness_no_type_error:
  well_typed_expr abi_bounds_env abi_good_encode /\
  env_consistent abi_bounds_env abi_bounds_context alias_state /\
  state_well_typed alias_state /\
  context_well_typed abi_bounds_context /\
  functions_well_typed abi_bounds_context /\
  accounts_well_typed alias_state.accounts /\
  call_evaluation_safe abi_bounds_context (int_calls_expr abi_good_encode) /\
  (!msg. FST (eval_expr abi_bounds_context abi_good_encode alias_state) <>
    INR (Error (TypeError msg)))
Proof
  simp[abi_bounds_env_consistent, abi_bounds_initial_state_well_typed,
       abi_bounds_context_preconditions, abi_good_calls_safe,
       abi_good_encode_result] >> EVAL_TAC >> simp[]
QED

(* Capacity and logical length are distinct runtime bounds. *)
Theorem abi_logical_length_runtime_error:
  FST (project_abi_operand abi_bounds_context
    (AbiMemory 0 0 alias_array_tv)
    (ValueSubscript (IntV 1))
    (SND (capture_abi_memory abi_bounds_context "a" alias_array_tv
      (ArrayV (DynArrayV [BoolV T])) alias_state))) =
    INR (Error (RuntimeError "ABI subscript dynamic bounds"))
Proof
  EVAL_TAC
QED

Theorem abi_negative_index_runtime_error:
  project_abi_operand cx (AbiMemory token off (ArrayTV tv bd))
    (ValueSubscript (IntV (-1))) st =
    (INR (Error (RuntimeError "ABI subscript bounds")),st)
Proof
  Cases_on `bd` >>
  simp[project_abi_operand_def, check_abi_projection_def,
       ignore_bind_def, bind_def, check_def, assert_def]
QED

Theorem abi_malformed_projection_still_type_error:
  project_abi_operand cx (AbiMemory token off (ArrayTV tv bd))
    (ValueSubscript (BoolV T)) st =
    (INR (Error (TypeError "ABI memory projection")),st)
Proof
  Cases_on `bd` >>
  simp[project_abi_operand_def, check_abi_projection_def,
       abi_subscript_offset_def, ignore_bind_def, bind_def,
       lift_option_type_def, return_def, raise_def]
QED

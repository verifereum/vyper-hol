(* Immutable Pop is rejected statically even in the initialization environment.
   The malformed raw AST still raises the deliberate runtime TypeError. *)
Theory vyperAbiImmutablePopTest
Ancestors
  list finite_map relation vyperAST vyperContext vyperState vyperInterpreter
  vyperAbiOperand vyperAbiAliasTest vyperTypeSystem vyperTypeInvariants
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeCallStackSoundness
  vyperTyping vyperValue
Libs
  wordsLib intLib

Definition abi_immutable_pop_context_def:
  abi_immutable_pop_context = empty_evaluation_context with <|
    stk := [(NONE,"main")];
    sources := [(0w,[(NONE,[VariableDecl Private Immutable "a" alias_array_type NONE])])]
  |>
End

Definition abi_immutable_pop_env_def:
  abi_immutable_pop_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY |+ ((NONE,"a"),alias_array_type);
    bare_global_assignable := FEMPTY |+ ((NONE,"a"),alias_array_type);
    toplevel_vtypes := FEMPTY |+ ((NONE,"a"),Type alias_array_type);
    type_defs := FEMPTY; fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Definition abi_immutable_pop_state_def:
  abi_immutable_pop_state = empty_state with <|
    scopes := [FEMPTY];
    immutables :=
      [(0w,[(NONE,FEMPTY |+ ("a",(alias_array_tv,ArrayV (DynArrayV [BoolV T;BoolV F]))))])]
  |>
End

Definition abi_immutable_pop_expr_def:
  abi_immutable_pop_expr = Pop (BaseT BoolT) (TopLevelNameTarget (NONE,"a"))
End

Definition abi_immutable_pop_encode_def:
  abi_immutable_pop_encode = TypeBuiltin (BaseT (BytesT (Dynamic 32)))
    (AbiEncode F NONE) (TupleT [BaseT BoolT]) [abi_immutable_pop_expr]
End

Theorem abi_immutable_pop_source_rejected:
  ~well_typed_expr abi_immutable_pop_env abi_immutable_pop_expr /\
  ~well_typed_expr abi_immutable_pop_env abi_immutable_pop_encode
Proof
  EVAL_TAC >> simp[]
QED

Theorem abi_immutable_pop_exact_type_error:
  FST (eval_expr abi_immutable_pop_context abi_immutable_pop_encode
    abi_immutable_pop_state) = INR (Error (TypeError "ABI immutable pop"))
Proof
  EVAL_TAC
QED

Theorem abi_immutable_pop_state_typed:
  state_well_typed abi_immutable_pop_state
Proof
  EVAL_TAC >> rw[] >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs(), value_has_type_def,
      well_formed_type_value_def, type_slot_size_def]
QED

Theorem abi_immutable_pop_env_consistent:
  env_consistent abi_immutable_pop_env abi_immutable_pop_context abi_immutable_pop_state
Proof
  EVAL_TAC >> rw[] >> EVAL_TAC >>
  gvs[FLOOKUP_UPDATE, find_var_decl_by_name_def, AllCaseEqs()]
QED

Theorem abi_immutable_pop_context_typed:
  context_well_typed abi_immutable_pop_context /\
  functions_well_typed abi_immutable_pop_context /\
  accounts_well_typed abi_immutable_pop_state.accounts
Proof
  rpt conj_tac >> EVAL_TAC >> simp[lookup_function_def]
QED

Theorem abi_immutable_pop_calls_safe:
  call_evaluation_safe abi_immutable_pop_context (int_calls_expr abi_immutable_pop_encode)
Proof
  rewrite_tac[call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"main")`, `[]`] >>
  simp[abi_immutable_pop_context_def, empty_evaluation_context_def,
       abi_immutable_pop_encode_def, abi_immutable_pop_expr_def, int_calls_expr_def,
       call_stack_follows_def, functions_follow_call_graph_def,
       calls_follow_call_graph_def, get_module_code_def,
       irreflexive_def, Once TC_CASES1, call_edge_rel_def,
       alias_array_type_def, empty_call_txn_def,
       lookup_function_def, lookup_callable_function_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), lookup_function_def]
QED

Theorem abi_immutable_pop_rejection_regression:
  ~well_typed_expr abi_immutable_pop_env abi_immutable_pop_encode /\
  env_consistent abi_immutable_pop_env abi_immutable_pop_context abi_immutable_pop_state /\
  state_well_typed abi_immutable_pop_state /\
  context_well_typed abi_immutable_pop_context /\
  functions_well_typed abi_immutable_pop_context /\
  accounts_well_typed abi_immutable_pop_state.accounts /\
  call_evaluation_safe abi_immutable_pop_context (int_calls_expr abi_immutable_pop_encode) /\
  FST (eval_expr abi_immutable_pop_context abi_immutable_pop_encode abi_immutable_pop_state) =
    INR (Error (TypeError "ABI immutable pop"))
Proof
  simp[abi_immutable_pop_source_rejected, abi_immutable_pop_env_consistent,
       abi_immutable_pop_state_typed, abi_immutable_pop_context_typed,
       abi_immutable_pop_calls_safe, abi_immutable_pop_exact_type_error]
QED

val () = let
  val th = DB.fetch "vyperAbiImmutablePopTest"
    "abi_immutable_pop_rejection_regression"
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print "ABI_IMMUTABLE_POP_REJECTION_KERNEL_CLOSED\n"
    else raise Fail "immutable Pop rejection is not kernel-closed"
  end;

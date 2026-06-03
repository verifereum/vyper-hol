# LEARNINGS_callable_entry_initial_state

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C2' tags=bind_arguments,env_scopes_consistent,initial_state,irule,witness-order
shape: Goal `env_scopes_consistent env_body cx (initial_state am [scope])` using theorem ending in `env_scopes_consistent env_body cx (st with scopes := [sc])`.
pattern: Bridge the record-shape mismatch by proving/sufficing `env_scopes_consistent env_body cx ((initial_state am [scope]) with scopes := [scope])`, simplify with `initial_state_def`, then `irule bind_arguments_env_scopes_consistent`. After `irule`, the generated existentials are ordered as args, tenv, vs; use `qexistsl [`args`, `get_tenv cx`, `vals`]` and then simplify/solve the parameter-map facts.
works_when: The current assumptions include `bind_arguments (get_tenv cx) args vals = SOME scope` and the three parameter-map facts exported by `functions_well_typed_callable_body_empty_static_maps`.
evidence:
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0059_t001
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0061_t001
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0063_t001
- episode:E0005

## L0002 scope='C1.4' tags=functions_well_typed,FEMPTY,static-maps,boundary-lemma
shape: Need callable body typing from `functions_well_typed cx` without using task-supplied static maps.
pattern: Package the use of `functions_well_typed_def` in a boundary lemma specialized to `fn_sigs` and `FEMPTY` for bare_globals/toplevel_vtypes/flag_members. `simp[]` discharges the empty finite-map side conditions; export only env field equalities, `type_stmts`, and parameter var-map facts needed downstream.
works_when: The consumer theorem only needs existence of some typing environment for the callable body, not one using the caller-supplied static maps.
evidence:
- episode:E0004
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0036_t001
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0039_t001

## L0003 scope='C3' tags=corollary,metis_tac,typed_stmts_no_type_error
shape: Goal `no_type_error_eval (eval_stmts cx body (initial_state am [scope]))` with hypotheses matching callable-entry theorem.
pattern: After proving `callable_entry_establishes_type_soundness_preconditions`, the no-TypeError callable-entry corollary can be a direct `metis_tac` over that theorem and `typed_stmts_no_type_error`; do not unfold runtime invariants or use lower-level statement soundness.
works_when: The assumptions exactly match the main callable-entry theorem and `typed_stmts_no_type_error` is in scope via vyperTypeSoundness.
evidence:
- episode:E0006
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0081_t001
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0082_t001

## L0004 scope='C4' tags=existential,empty_context,FEMPTY,record,qualified_defs
shape: Existential satisfiability of `functions_well_typed`, `context_well_typed`, `state_well_typed`, `env_consistent`, and `type_stmts env NoneT []`.
pattern: Use `empty_evaluation_context`, empty `typing_env` records, `initial_state initial_machine_state [FEMPTY]`, and simplify definitions. For irrelevant existentials use `ARB`; qualify external simplification theorems like `vfmStateTheory.empty_accounts_def` and `vyperStateTheory.lookup_scopes_def` when unqualified names are not imported.
works_when: The statement only requires existence of soundness preconditions for an empty statement list and does not relate the abstract-machine existential to the chosen state.
evidence:
- episode:E0007
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0105_t001
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0112_t001

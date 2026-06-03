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

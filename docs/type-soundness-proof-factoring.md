# Type-Soundness Proof Factoring Opportunities

This note records cleanup opportunities identified while extending machine-typing preservation for checked calls and deployment (issue #440). These are follow-up proof-engineering tasks, not prerequisites for completing #440 unless explicitly noted.

The main concentration of debt is `semantics/prop/vyperTypeContractSoundnessScript.sml`, which currently combines deployment readiness, call-prefix safety, getter reasoning, and body preservation. Any cleanup should preserve theorem coverage and proceed incrementally with `holbuild`.

## Immediate factoring used by #440

The current deployment proof needs a focused theorem that composes existing results into post-constant immutable readiness:

```sml
checked_deployment_constants_establish_immutables_ready
```

It should reuse:

- `deploy_constants_setup_bare_globals_ready`;
- `check_contract_toplevel_vtypes_consistent_initial`;
- `check_contract_bare_globals_consistent_initial`;
- `immutables_ready_env_immutables_consistent`.

This is part of the active work rather than deferred cleanup. The existing `deployment_setup_immutables_ready` is close in shape, but its `constants_do_not_clobber_bare_globals` premise is intended for immutable-only maps and does not directly fit an artifact map whose bare globals also contain constants.

## Deferred cleanup opportunities

### 1. Transport `immutables_ready` as a predicate

Deployment readiness is currently transported one clause at a time in `vyperTypeContractSoundnessScript.sml`. The pipeline includes:

- `deploy_constants_setup_bare_globals_ready`;
- `deploy_call_success_transports_bare_global_readiness_clause`;
- `deploy_context_constants_bare_globals_type_ready`;
- `deploy_call_success_scalar_bare_global_type_from_constants`;
- `deploy_constructor_success_bare_global_type_from_constants`;
- `load_contract_deployed_bare_globals_immutables_ready_clause`;
- `deployed_toplevel_vtypes_immutables_ready_clause`;
- `deploy_context_constants_bare_globals_lookup_exists`;
- `call_external_function_deploy_success_final_lookup_exists_from_constants`;
- `load_contract_deployed_bare_globals_immutables_ready_exists_clause`;
- `load_contract_establishes_immutables_ready`.

Prefer a predicate-level preservation boundary such as:

```sml
call_external_function_deploy_success_preserves_immutables_ready
```

Then derive the scalar lookup/type-tag corollaries only where independently useful. The final `load_contract_establishes_immutables_ready` theorem should become a short composition proof.

### 2. Consolidate constant-evaluation machine preservation

Constant-evaluation preservation is spread across several theories:

- `evaluate_all_constants_preserves_accounts` in `vyperTypeEntryReadinessScript.sml`;
- `evaluate_all_constants_preserves_machine_static_components` in `vyperTypeDeploymentMachineScript.sml`;
- local `evaluate_all_constants_preserves_layouts` in `vyperTypeContractSoundnessScript.sml`;
- immutable lookup/type preservation in `vyperTypeInitialStateScript.sml` and `vyperTypeContractSoundnessScript.sml`.

Provide one reusable component theorem covering at least:

```text
accounts, sources, exports, layouts
```

Keep the representation-sensitive immutable lookup lemmas in `vyperTypeInitialStateScript.sml`. Derive layouts-only and accounts-only results as corollaries if downstream scripts still benefit from those interfaces.

### 3. Retire or derive the `_c53` call-prefix pipeline

`vyperTypeContractSoundnessScript.sml` contains an older family including:

- `send_call_value_preserves_scopes_c53`;
- `call_lock_action_preserves_accounts_c53`;
- `call_lock_action_preserves_scopes_c53`;
- `call_lock_send_prefix_body_state_ready_c53`;
- `call_lock_action_no_control_c53`;
- `call_lock_action_no_type_error_c53`.

Later sections contain overlapping non-`c53` results, including:

- `send_call_value_preserves_scopes`;
- `call_lock_action_preserves_scopes`;
- `call_lock_send_prefix_body_state_ready`.

Audit downstream uses. Prefer one general theorem family, with old statements derived as corollaries where compatibility is needed. Do not delete the older proofs until all callers have migrated and the replacement has built successfully.

### 4. Unify static-context congruence lemmas

`vyperTypeContractContextScript.sml` contains stack-specific preservation lemmas for:

- function-signature consistency and declared completeness;
- top-level type completeness;
- bare-global completeness;
- bare-global assignability completeness;
- flag-member completeness.

`vyperTypeContractSoundnessScript.sml` later contains a parallel `*_context_cong` family for the same components, plus `env_context_consistent_context_cong`.

Prefer one public static-context equivalence/congruence theorem. Stack irrelevance and initial-context variants should be short corollaries. This would also remove repeated unfolding of `env_context_consistent_def`.

### 5. Factor the explicit-function/getter machine pipelines

`vyperTypeExternalCallMachineScript.sml` separately develops explicit-function and getter paths through body execution, send/value transfer, lock handling, release, and machine reconstruction.

The body-typing inputs legitimately differ, but both paths eventually expose the same preservation interface:

```text
state_well_typed st' /\ accounts_well_typed st'.accounts
```

Introduce a generic post-prefix body/component boundary and keep explicit/getter selection as thin adapters. Avoid abstracting over semantic differences merely to shorten scripts; factor only the shared reconstruction and preservation layers.

### 6. Reduce repeated static-map fold hierarchies

`vyperTypeContractStaticMapsScript.sml` repeats a similar proof hierarchy for function signatures, top-level value types, bare globals, bare-global assignability, and flag members:

```text
add_toplevel: sound / complete / preserve
add_module:   sound / complete / preserve
add_contract: sound / complete / preserve
artifact/check_contract boundary
```

Investigate generic finite-map fold preservation and completeness lemmas. This is a larger refactor: keep map-specific semantic soundness statements, but factor the common fold/update mechanics. Do not combine this work with #440.

### 7. Split `vyperTypeContractSoundnessScript.sml` by responsibility

The file currently contains more than 3,000 lines spanning:

- deployment constant and immutable transport;
- external-call no-type-error/control proofs;
- getter context equivalence;
- body component preservation;
- load-contract readiness.

Potential extractions are:

1. deployment immutable readiness and transport;
2. call-prefix control/type safety;
3. getter context equivalence.

New files should expose small top-level APIs and preserve a clear dependency direction. Avoid moving code solely for file size; extract coherent theorem clusters after their shared interfaces are identified.

## Cleanup process

For each cleanup:

1. Identify all theorem users before changing visibility or statements.
2. Add the general theorem first.
3. Re-prove existing public statements as corollaries.
4. Migrate callers incrementally.
5. Build each affected theory with `holbuild`.
6. Remove old local implementations only after migration succeeds.
7. Check that no cheats or `CHEAT` warnings were introduced.

These refactors should not weaken invariants or alter interpreter semantics.

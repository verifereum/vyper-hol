# Shared source-module signatures and contexts

These theories provide source legality, resolution, signatures and module
contexts for the [ordinary paired frontend](constant-evaluation.md), without
independent source-body inference.

## Interfaces

- `sourceModuleDefs`: error/result types, policies, bind/collect, annotation and
  type resolution, argument/local bindings, strict expression validation.
- `sourceModuleEnv`: canonical module IDs, nominal identities/definitions and
  slot trust; builtin scopes, runtime/event bindings and policy contexts.
- `sourceModuleSignature`: decorators, visibility/mutability, variables/events/
  interfaces, `source_module_signature`, `source_module_signatures`,
  `source_module_policy_signature`, `source_module_policy_signatures`, and
  `source_module_function_context`. Private signature FunctionDecls carry empty
  bodies and default-arity placeholders; these are not executable output.
- `sourceModuleLink`: structural uses/initializes/exports/implements checks,
  dependency ordering, export expansion and original-default identity.
- `sourceModuleOverride`: nominal/parameter/default compatibility, policy-aware
  override linkage, transitive call-target rewriting and cycle rejection.
- `sourceModuleContext`: `source_module_policy_signature_modules`,
  `source_module_signature_context`, `source_module_policy_signature_context`,
  `source_module_link_program` and `source_module_link_program_equations`;
  shared bind-success/retention lemmas. Context construction never translates
  statements or executable function bodies.

`sourceOrdinaryProgram` consumes these shared interfaces. It checks nominal
signature-environment agreement, traverses original bodies with paired
occurrence claims, retains exact source/modules and calls `check_contract T` on
those modules. Its compile callback receives the same checked modules, including
deployment bodies. No multi-module flattening is introduced.

## Trust and limits

Canonical IDs, nominal environment, storage slots/layouts and residual runtime
contexts remain explicitly inherited. Loader provenance is not authenticated;
see [sourceModuleLoader.md](sourceModuleLoader.md). Constant values and original
bounds/defaults are computed, not inherited folded metadata.

`sourceExprElaborate` remains the strict contextual expression validator needed
by ordinary folding and signature constants. It is not a general independent
body typer. There are no base `source_module_elaborate`, `source_module_check`,
`source_module_compile`, `Source` facade or artifact-semantic adapters.

Shared link/policy/loader tests remain in `sourceModuleLinkTest`,
`sourceModulePolicyTest` and `sourceModuleLoaderTest`. Ordinary complete-module,
artifact, metadata-invariance and backend comparisons are described in
[ordinary frontend regressions](../tests/sourceOrdinaryAcceptance.md).

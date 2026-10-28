# Opt-in resolved source constant environments

`sourceConstEnvTheory.source_const_resolve seed declarations` consumes:

- a seed association list of `(resolved declaration path, binding)`;
- a declaration list of `(resolved declaration path, original source initializer)`.

Paths are **component lists**, compared structurally. They are not raw names,
joined dotted strings, or Vyper `source_id` values. `SCE_Name` operands must have
already undergone lexical/module resolution. Imported aliases denoting the same
declaration must use the same path. Locals, parameters and immutables must be
represented by their own resolved identities with `SC_DynamicBinding`, or by
`SCE_Dynamic`; they must not be seeded as constants merely because their
initializer is constant. The seed's constant provenance is a caller obligation.

This API is module-independent and opt-in. It neither implements JSON
import/alias canonicalization nor changes the ordinary frontend. It does not
prove source typing, reification, checker/deployment agreement or module type
environment preservation.

## Processing and outcomes

1. Reject empty paths/components, duplicate identities (including collisions
   between seeds and declarations), and invalid seed values.
2. Discover **all** name dependencies, including builtin type operands,
   keywords, unknown calls, unsupported children and Boolean branches. Report
   missing identities with the owning declaration before graph processing.
3. Select the first declaration whose name dependencies are already bound.
   Dynamic seed bindings count as bound, not as constants. Evaluate its original
   expression with `source_const_eval`. Append only a validated computed value.
4. Recur on the remaining declarations. Termination is proved by their strictly
   decreasing length; there is no arbitrary retry/resource budget.

`SCEnv_Resolved` returns the seed followed by evaluated declarations in stable
first-ready order. Required declarations with genuinely dynamic expressions
return `SCEnv_NotConstant`; invalid arithmetic and unsupported constructs return
`SCEnv_Invalid` and `SCEnv_Unsupported` respectively. They are not retry/cycle
outcomes. Evaluation retains the evaluator's eager child-error behavior.

`SCEnv_Cycle` reports the blocked region after no declaration is ready. This
region includes any dependents of cycles; it is **not** a simple directed-cycle
witness. Missing identities have already been excluded by the public entry
point. Error constructors do not expose a successful partial environment.
Validation and first-ready declaration order determine diagnostic precedence;
this is not a claim of exact pinned compiler diagnostic ordering.

## Local invariants and tests

`sourceConstEnvPropsScript.sml` establishes the picker length/decomposition and
blocked-dependency contracts, append-only resolution, preservation of every seed
lookup (including dynamic bindings), validated result bindings, and unique
canonical keys with exactly the seed/declaration domain. Added entries are only
constants; every dynamic result binding originates in the seed. Evaluation of
already-bound expressions is invariant under successful extension. Every resolved
declaration's value agrees with its original initializer evaluated in the final
environment (`source_const_resolve_initializer_values`). No leaf-spelling lookup
or joined-string comparison occurs.

`sourceConstEnvTestScript.sml` contains kernel-computed regression theorems for
forward/backward and cross-module resolved references, nested component paths,
same-leaf/dotted-path separation, missing paths, cycles and their dependents,
duplicates, bad seeds/identities, runtime shadowing/immutables, eager failures,
keywords/callees, type operands, decimals and aggregates. The test theory audits
every export of all three new theories for open hypotheses, nonstandard axioms
and oracle tags other than `DISK_THM`.

Build explicitly (no existing build-root files are changed):

```
.agent-files/.holbuild-toolchain/bin/holbuild frontend/sourceConstEnvTestScript.sml --tactic-timeout 2.5
```

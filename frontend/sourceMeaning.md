# Independent staged source meaning

## Boundary

The opt-in `sourceMeaning*` theories define source meaning independently of
emitted runtime syntax. They do not redirect ordinary frontend entry points or
weaken backend preconditions. See [constant-evaluation.md](constant-evaluation.md)
for the cross-cutting design and trust boundary, and
[sourceMeaningLocation.md](sourceMeaningLocation.md) for location-sensitive forms.

`VYPER_PIN` determines the source arithmetic specification, described in
[sourceConstCore.md](sourceConstCore.md) and
[sourceConstBuiltin.md](sourceConstBuiltin.md). Conservative Decimal and power
envelopes remain in force. These theories do not prove equivalence to Python,
the full pinned compiler, or bytecode execution.

## Semantic interfaces

* `sourceMeaningConst` evaluates every `source_const_expr` constructor
  mathematically without calling `source_const_eval`, elaboration, reification
  or a runtime AST evaluator. It shares the scalar operator/domain and error
  algebra: Decimal rounding, hashing, power guards and scalar primitives are
  **not independently reimplemented**.
* `sourceMeaningDefs` derives staged semantic terms from original syntax.
  Constant subtrees resolve and evaluate mathematically; dynamic names, unary
  operations, non-shift binary operations, conditionals and arbitrary-length
  Boolean chains recursively derive their children. Evaluation uses runtime
  primitives with left-to-right state threading, materialisation and exceptions.
* `sourceMeaningValue` independently denotes scalars, nested tuples and
  fixed/dynamic arrays, without a reifier or emitted code. Its bridge preserves
  the entire state. The empty nominal-map boundary excludes nominal structs.
* `sourceMeaningCode` relates semantic terms to runtime expressions. This is a
  compilation bridge, **not the definition of source meaning**.
* `sourceMeaningEffects` gives a resolved-declaration rule for `raw_revert(data)`.
* `sourceMeaningEnv` uses finite, fresh dependency derivations of independent
  initializer meanings. Their domain is exactly the seed plus declarations;
  cycles/self-references cannot acquire invented fixed-point values. Fresh
  extension preserves existing lookups and evaluations of ready expressions.
* `sourceMeaningStmtDefs` gives original-source body rules and independent store
  computations; neither calls an elaborator or `eval_expr`/`eval_stmt`/`eval_stmts`.
* `sourceMeaningProgramDefs` selects original declarations, requires independent
  constant initializer values and finite dependencies, and resolves retained
  entry argument/return annotations.

Staging is semantic: mathematical constant subtrees are evaluated before their
surrounding dynamic runtime operations. They are not silently replaced by
width-bounded runtime evaluation of the original arithmetic.

## Theorem contracts

| Theorem | Contract |
|---|---|
| `source_meaning_const_correct` | Exact evaluator/independent meaning equality for all four outcomes |
| `source_meaning_reify_evaluates` | Successful scalar reification evaluates to the denoted value with the entire state unchanged |
| `source_meaning_code_evaluates` | Code relation, type agreement and runtime binding denotation imply equality of complete computations |
| `source_meaning_build_code` | Independent derivation, binding-type agreement and successful build imply the code relation |
| `source_meaning_elaboration_sound` | Successful elaboration equals independent staged evaluation at every initial state, including errors and final states |
| `source_meaning_replacement_equal` | Code related to the same staged meaning has equal results and final states |
| `source_meaning_add_runtime`, `source_meaning_add_replacement` | Explicit integer-width compatibility relates mathematical addition to runtime literal addition and its replacement |
| `source_meaning_revert_sound` | Resolved intrinsic and data-type inference contracts imply complete computation equality for `raw_revert` |
| `source_meaning_name_substitution` | Resolved constant identity and valid-value binding give the meaning of an original named reference |
| `source_meaning_code_evaluates_on` | Binding agreement is required only for identities read by the meaning |
| `source_meaning_body_transport` | Successful statement elaboration implements original-source body rules and preserves context/cell agreement through local extensions |
| `source_meaning_program_constants_transport` | Registry constant resolution yields independent declaration meanings and a finite dependency derivation |
| `source_meaning_staged_extension` | Fresh dependencies preserve resolved defaults/initializers whose dependencies were already bound |
| `source_meaning_function_transport` | Original function meaning and successful elaboration imply equal body-entry execution |
| `source_meaning_compile_entry` | Checked/compiled modules retain the selected emitted declaration, its body simulation and the actual `compile_vyper` equation |
| `source_meaning_constant_exists`, `source_meaning_constant_return_exists` | Successful constant expression/single-return elaboration constructs independent meanings; the return theorem also gives all-state body execution |
| `source_meaning_policy_elaborate_member` | Policy-aware elaboration supplies independent constant dependencies and retained body-phase membership |
| `source_meaning_policy_program_transport` | General-policy elaboration transports independently derived declarations with source-policy-adjusted locks |
| `source_meaning_exported_call_transport` | Ordinary imported external dispatch agrees with independent invocation, including combined modules/type environment and pending-deletion finalization |

`source_meaning_binding_types` is a real hypothesis: independently supplied
source dynamic types must match the runtime binding code. Semantic environments
map resolved identities to state computations. Runtime bindings must denote
those computations at **all threaded states**, not just at entry. This does not
follow from elaboration, and binding code need not be pure. No state
well-typedness assumption is needed for computation equality.
`source_meaning_local` and `source_meaning_local_agreement` give concrete,
AST-free local-name denotation and its runtime `Name` agreement.

General soundness requires an independent derivation and successful elaboration.
Existence results construct derivations for supported constant, initializer and
constant-return elaborations; they are not completeness for every accepted
frontend expression or program.

## Expression scope

The pure relation covers the entire constant core (including aggregates,
supported builtins, eager failures and explicit unsupported outcomes), recursive
constant replacement, resolved dynamic names/module paths, unary and non-shift
binary operations with their source-domain checks, conditionals and Boolean
chains. Runtime Boolean chains short-circuit, but compile-time errors in children
remain eager. Dynamic operations retain runtime overflow/error behavior.

Fully constant mathematical shifts are covered. Dynamic shifts are outside the
same-operand-type rule because their RHS is independently typed/reified. The
integer-addition replacement theorem requires its explicit width condition;
Decimal, power, shifts and other operators do not inherit it. Unbounded source
intermediates prohibit arbitrary pre-normalisation runtime-AST equivalence.

The `raw_revert` theorem requires independent declaration/intrinsic bindings and
`source_expr_infer ... data = SOME data_ty`; general inference transport is not
proved. It preserves the interpreter's evaluation of data followed by
`Error (RuntimeError "raw_revert")`, not EVM revert-payload semantics.

Dynamic comparisons/aggregates, subscripts, runtime builtins, ABI operations,
`raw_call`, and storage/immutable assignments use the separate
[location-sensitive relation](sourceMeaningLocation.md), not the pure relation.
General inference/type/module completeness and arbitrary environment agreement
remain outside these results.

## Bodies and compiler artifacts

`source_meaning_body` / `source_meaning_bodies` cover `Pass`, returns (including
bare returns), initialized non-interface locals, simple local-name assignments,
nested `If` and sequencing. Expression children use original-source meanings.
Local declaration type resolution is shared with the source type phase, not an
independent type checker. Unsupported forms have no derivation.

`source_meaning_locals` relates each local identity/type to
`Name ty (LAST path)` in the binding table and extends through declarations.
Unreferenced global/builtin bindings need no all-binding denotation hypothesis.
Store equality includes scopes, storage, ABI memory, exceptions and effects.
Independent body evaluation includes branch scope push/finally-pop and assignment
ABI writes; it does not assume successful execution to suppress errors.

`source_meaning_entry` selects an original declaration with original module
scopes, constants and annotations. Execution begins at **body entry**, with
argument cells supplied. `source_meaning_elaborate_member` establishes retained
membership; `source_meaning_compile_entry` composes body simulation with genuine
checking (including constructors) and the actual raw compiler result for those
same modules. This is compiler-artifact composition, **not bytecode correctness**.
Existing backend simulation hypotheses/admissions remain unchanged.

## Source-selected calls and loading

`sourceMeaningCallDefs` retains source names, decorators, argument/return
annotations, default syntax and bodies. Private scalar/aggregate constants use
original initializer meanings. `source_meaning_parameters_locals` establishes
actual parameter cell bindings rather than assuming a caller-supplied scope.

`source_meaning_call` selects independently source-derived declarations, not
emitted code. `source_meaning_invoke` stages the required default suffix in an
empty scope, binds arguments, handles locks/value checks, runs the independent
body and casts returns, retaining rollback, errors and request traces.
`source_meaning_globals` installs recursive source values into runtime cells;
`source_meaning_globals_transport` / `source_meaning_install_transport` equate
this with actual initializer execution uniformly over states.
`source_meaning_load` includes immutable allocation, installation, constructor
dispatch and source/exports installation, including a synthetic empty payable
constructor when none is declared.

`source_meaning_declaration_transport` and `source_meaning_module_transport`
lift independent declaration meanings through successful body-phase elaboration.
`source_meaning_call_transport` / `source_meaning_load_transport` equate complete
interpreter API results. `source_meaning_compile_program` composes these with
the public original-source compiler wrapper, retaining original identity,
genuine checking and exact compiler equations. Independent module derivation
and equality with the supplied nominal type environment remain explicit.

Load/constructor transport covers one module with private scalar/aggregate
constants and source-derived functions with supported bodies/defaults. It is not
arbitrary multi-module deployment, storage/immutable initializer coverage,
public getter coverage, nominal-type completeness or nested-call completeness.

## Policies and imported entry calls

`sourceMeaningPolicy` extracts independent finite constant dependencies from
public `source_module_elaborate`, including imports, and retains linkage,
export, override, signature and body evidence. The policy-free API is named
`*_simple`; it is not substituted for general-policy success.

`sourceMeaningPolicyDecl` derives lock behavior from original decorators,
visibility and mutability: pure functions have no lock, and explicit `reentrant`
opts out of inherited external defaults. Policy transport still requires source
function/body derivations. Declaration-only interface modules are excluded from
this executable-declaration theorem.

`sourceMeaningModules` handles ordinary imported external entry invocation with
the full module set and nominal environment. Defaults, argument binding, locks,
value checks, casts/errors, rollback and final pending deletions are included.
This removes the single-module restriction for nondeployment entry calls, not
for loading. It does not establish nested call-expression meanings, getters,
imported deployment/immutable initialization, loops or general source typing.

## Reproduction

From the repository root:

```sh
holbuild build sourceMeaningProgramTestTheory sourceMeaningCallTestTheory \
  sourceMeaningCheckedTestTheory sourceMeaningAggregateTestTheory \
  sourceMeaningExportTestTheory sourceMeaningWitnessTestTheory \
  sourceMeaningLocationTestTheory sourceMeaningLocationWitnessTestTheory \
  --skip-checkpoints --tactic-timeout 2.5
```

These roots exercise original-source derivations, elaboration and all-state
transport, staged eager errors versus runtime short-circuiting, aggregates,
defaults/constructors and imported dispatch. Their export audits reject open
hypotheses, axioms and oracle tags other than `DISK_THM` bookkeeping. Such an
audit is not a force-rebuild or certification of the backend dependency closure;
test examples do not establish universal frontend completeness. See the
location-sensitive document for the fixed body-inventory contract.

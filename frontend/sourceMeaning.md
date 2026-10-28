# Independent staged source meaning (opt-in)

## Authority and boundary

`VYPER_PIN` is authoritative: **cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c**.
The local `/home/lukasz/vyper` checkout was checked at that revision. Source
arithmetic follows `vyper/semantics/analysis/constant_folding.py`, the operator
methods in `vyper/ast/nodes.py`, and the Decimal context in `vyper/utils.py`, as
specified in [sourceConstCore.md](sourceConstCore.md) and
[sourceConstBuiltin.md](sourceConstBuiltin.md). Their existing conservative
Decimal and power envelopes remain in force. No theorem here proves equivalence
to execution of Python, the full pinned compiler, or bytecode.

These are **new, opt-in `sourceMeaning*` theories**. This extension does not
modify ordinary expression/module implementations or backend preconditions.
The original program/call/checked roots remain; aggregate, exported-call and
witness-inventory roots extend their tested frontier below. The subsequent
[location-sensitive extension](sourceMeaningLocation.md) adds independent ABI,
reference/subscript, builtin and body meanings for all 40 original #543 bodies;
it leaves the original pure relation and its frozen 21-body test unchanged.

## Independent definitions

* `sourceMeaningConst`: syntax-directed mathematical evaluation of every
  `source_const_expr` constructor. It does not call `source_const_eval`, an
  elaborator, reification, or a runtime AST evaluator. It shares the pinned
  **scalar operator/domain and error algebra** with the source constant core;
  it is not a second independent implementation of Decimal rounding, hashing,
  power guards, or the scalar arithmetic primitives.
* `sourceMeaningDefs`: independent source derivation rules and staged semantic
  terms (`source_meaning`). The constant rule resolves and evaluates the
  **original source**, denoting scalar or recursively structured values.
  Dynamic name, unary, non-shift binary, conditional and arbitrary-length
  Boolean-chain rules refer to original syntax and recursively derived children. They never mention successful
  elaboration, emitted code, or reification. Evaluation of these terms uses
  runtime primitives directly, with left-to-right state threading,
  materialisation, exceptions and conditional branch selection.
* `sourceMeaningValue`: independent, type-directed denotation of scalar values,
  nested tuples and fixed/dynamic arrays. The definition uses neither a reifier
  nor emitted code. Its bridge proves all-state evaluation with no state change.
  The empty nominal-map boundary deliberately excludes nominal structs.
* `sourceMeaningCode`: a separate compilation relation between those semantic
  terms and runtime expressions. This is a proof bridge, **not the definition
  of source meaning**. In particular, source rules are not of the form “if
  elaboration returned this runtime AST, its meaning is evaluating that AST.”
* `sourceMeaningEffects`: independent resolved-declaration rule for the
  currently implemented `raw_revert(data)` source call, plus its soundness.
* `sourceMeaningEnv`: finite, fresh dependency derivations using independent
  initializer meanings. Unlike simultaneous initializer equations, these cannot
  give self-references/cycles invented fixed-point values. Successful dependency
  resolution constructs such a derivation; its domain is exactly seed plus
  original declarations. Fresh derivations also preserve existing lookups and
  evaluations of ready expressions under environment extension.
* `sourceMeaningStmtDefs`: source-directed recursive body rules and separate
  store computations for declarations, local assignment, branches, sequencing,
  and returns. Neither the rules nor these computations call `eval_expr`,
  `eval_stmt`, `eval_stmts`, or an elaborator.
* `sourceMeaningProgramDefs`: original program/declaration selection and constant
  denotation. All original constant initializers must resolve and have their
  independent mathematical values; a finite dependency derivation is required.
  Entry arguments/return annotations are resolved from retained source syntax.

Staging is deliberate: a constant subtree is interpreted with mathematical
source arithmetic before a surrounding dynamic operation executes with runtime
arithmetic. The theorem does **not** silently evaluate every original constant
subtree as width-bounded runtime arithmetic instead.

## Frozen small contracts

| Theorem | Contract |
|---|---|
| `source_meaning_const_correct` | Exact evaluator/independent meaning equality, **all four outcomes**, by source structural induction |
| `source_meaning_reify_evaluates` | Scalar source value/literal plus successful reification gives the specified value and **unchanged entire state** |
| `source_meaning_code_evaluates` | Code relation plus type-context and runtime-binding denotation agreement gives equality of complete computations |
| `source_meaning_build_code` | Independent source derivation plus binding-type agreement and successful build gives the code relation |
| `source_meaning_elaboration_sound` | Public elaboration equals independent staged source evaluation at **every initial state**, including error results and complete final states |
| `source_meaning_replacement_equal` | Elaborated code and any code related to the same staged source term have equal results/final states |
| `source_meaning_add_runtime` | Explicit integer-width compatibility connects unbounded source addition to a runtime addition of literals |
| `source_meaning_add_replacement` | Under that width condition, replacing an unfurled runtime literal addition by the reified mathematical result preserves result/state |
| `source_meaning_revert_sound` | Resolved intrinsic and data-type inference contracts give complete computation equality for `raw_revert` |
| `source_meaning_name_substitution` | Resolved constant identity and valid-value binding give the staged meaning of an original named reference |
| `source_meaning_code_evaluates_on` | Agreement is needed only for identities actually read by the source meaning, not unrelated module code |
| `source_meaning_body_transport` | Successful statement elaboration implements original-source body rules, preserves static context/cell agreement through local extensions, and equates complete state computations |
| `source_meaning_program_constants_transport` | Successful registry constant resolution gives independent meanings for every original source declaration, plus finite dependency derivation |
| `source_meaning_staged_extension` | Resolved original default/initializer outcomes are preserved under fresh finite dependency extension when their dependencies were already bound |
| `source_meaning_function_transport` | Original source function body and successful function elaboration give equal body-entry execution |
| `source_meaning_compile_entry` | The checked/compiled modules contain the emitted declaration whose body implements the selected original source entry; actual `compile_vyper` result is retained |
| `source_meaning_constant_exists` | Successful constant-stage expression elaboration constructs a source meaning and independently denoted value; no supplied source derivation |
| `source_meaning_constant_return_exists` | Accepted original constant single-return body constructs its independent meaning and proves all-state body execution |
| `source_meaning_policy_elaborate_member` | Actual policy-aware elaboration gives independent original constant dependencies and retained body-phase membership |
| `source_meaning_policy_program_transport` | Actual general-policy phase transports independently derived declarations with source-policy-adjusted lock metadata |
| `source_meaning_exported_call_transport` | Imported ordinary external dispatch, with combined modules/type environment and pending-deletion finalization, agrees with independent source invocation |

`source_meaning_binding_types` is a **real hypothesis**: each independently
supplied source dynamic declaration type must have runtime binding code with
that type. Semantic environments independently map resolved identities to
state computations. The soundness theorem additionally requires the actual
runtime binding code to denote those computations at **all threaded states**,
not just the initial state. It does not derive environment correctness from
successful elaboration or assume purity of binding code. No state well-typedness
assumption is needed for the equality theorem. `source_meaning_local` and
`source_meaning_local_agreement` give a concrete, AST-free local-name denotation
and its agreement with runtime `Name` lookup.

The source relation itself specifies the proved fragment. General soundness is
conditional on an independent derivation and successful elaboration. Staged
existence theorems additionally construct derivations from successful constant,
initializer and constant-return elaboration, rather than assuming semantic
readiness. The witness test constructs recursive derivations directly from
original syntax. Neither these results nor the rules claim complete source typing
or meanings for every successful frontend expression.

## Exact coverage and limitations

**Proved:**

* Mathematical constant evaluation for the whole existing source constant core,
  including eager failure propagation, aggregates, supported builtins and
  explicit unsupported outcomes.
* Scalar and aggregate constant replacement: Int, Bool, Decimal, String, Bytes,
  Hex, nested tuples and arrays, including compound compile-time arithmetic.
  Aggregate declaration meanings and recursive global-cell installation are
  transported as well.
* Dynamic resolved names/module paths, unary and binary source operators with
  their existing source-domain checks, recursive conditional expressions and
  arbitrary-length runtime Boolean chains. Boolean chains short-circuit at
  runtime, but do not bypass eager compile-time errors in their children.
  Dynamic operator evaluation retains runtime error/overflow behavior. Dynamic
  shifts are now explicitly outside this same-operand-type rule: frontend shift
  elaboration independently types/reifies its RHS. Fully constant mathematical
  shifts remain covered. No false same-type shift transport is asserted.
* `raw_revert` as a separate source-call theorem. Its source declaration kind,
  intrinsic binding and child meaning are independent hypotheses. The equality
  `source_expr_infer ... data = SOME data_ty` is explicit: **general source-type
  inference transport is not proved**.
* Constant-environment transport under agreement on referenced declarations;
  successful dependency-resolved initializer values in the resulting environment;
  extensional semantic-environment transport. These are declaration/environment
  facts. The additional program/body frontier below proves partial execution.

**Not proved by the source-to-runtime fragment:**

* In the **original pure relation**: dynamic comparisons/aggregates, subscripts,
  runtime builtins, ABI encode/decode, `raw_call`, and storage/immutable assignments.
  The separate [location-sensitive relation](sourceMeaningLocation.md) now covers
  these forms at its explicit source-rule boundary, including all fixed #543
  bodies. Nominal structs, general nested calls, loops and arbitrary multi-module
  deployment simulation remain outside this extension. Ordinary imported entry
  dispatch is a separate proved frontier, not nested-call source completeness.
* General inference/type/module completeness; establishment of environment
  agreement for arbitrary frontend-produced code.
* Arbitrary pre-normalisation runtime-AST equivalence for constant expressions.
  Mathematical intermediates can exceed runtime bounds. Integer addition has a
  separate explicit width-compatible replacement theorem; Decimal, power,
  shifts and other operators do not inherit that theorem.
* Full EVM revert-payload behavior: the current interpreter evaluates the data
  then raises `Error (RuntimeError "raw_revert")`; the effect theorem preserves
  **that existing interpreter behavior**, not a stronger payload model.

## Partial program execution frontier

`source_meaning_body` / `source_meaning_bodies` cover `Pass`, returns (including
bare returns), initialized non-interface local declarations, simple local-name
assignments, nested `If`, and lists. Expression children use the independent
original-source relation; named constants are substituted mathematically.
Local declaration type resolution is shared with the source type phase; this
is not a new independent source type checker. Unsupported statement forms have
no semantic derivation, rather than an opaque readiness premise.

`source_meaning_locals` is an explicit cell-layout relation: each source local
identity/type maps to `Name ty (LAST path)` in the runtime binding table.
Its extension lemma establishes this relation for new declarations. Unreferenced
global/builtin bindings need no arbitrary all-binding denotation hypothesis.
The store relation is equality of the *whole* interpreter state at entry and
exit (including scopes, storage, ABI memory, exceptions and effects), not merely
equality of return values. The body evaluator independently invokes store
primitives, including branch scope push/finally-pop and assignment ABI writes.
It does not assume well-typed states or successful execution to suppress errors.

`source_meaning_entry` selects an original declaration in an original program,
with source module scopes/table, source constants and source argument/return
annotations. Execution starts at **body entry**, with argument cells supplied.
`source_meaning_elaborate_member` proves actual elaboration emits the selected
declaration into the retained module set; `source_meaning_compile_entry` carries
this transport together with genuine checking (constructors included) and the
actual raw compiler result for the same modules. This is compiler-*artifact*
composition plus body simulation, **not an EVM/bytecode correctness theorem**.
Existing backend simulation hypotheses/admissions remain untouched. The newer
call frontiers below extend this body-entry theorem; ABI decoding, arbitrary
function-call expressions and general layout/type provenance remain outside it.

Kernel examples use a real original program declaring `N = 1 + 2` and a function
with arguments, `y: uint256 = N`, a dynamic Boolean branch, `y = x + N` or `y = N`,
and `return y`. They prove original-program meaning, actual module elaboration,
all-state body transport, and concrete execution: with `x=4`, the two branches
return 7 and 3, preserve all unrelated state, retain the assigned outer cell,
and remove the temporary branch scope. This is a reachable, nonvacuous partial
program, not just a pair of elaborator-output equations.

## Source-selected call and constructor frontier

`sourceMeaningCallDefs` gives independent source declaration denotations. Function
names, decorators, argument/return annotations, default syntax and original bodies
are retained. Functions use the body rules above; private scalar and aggregate
constants use original initializer meanings. Parameter identity/type lists are constructed from
source arguments, and `source_meaning_parameters_locals` proves their actual cell
bindings, rather than assuming a caller-supplied body-entry scope.

`source_meaning_call` selects a function from these source denotations, **not from
elaborated code**. `source_meaning_invoke` stages the required default suffix in an
empty scope, binds provided/default values, handles locks and call value, runs the
independent body, casts returns, and retains rollback/errors/request traces.
`source_meaning_globals` installs scalar and aggregate source values into runtime cells;
`source_meaning_globals_transport` and `source_meaning_install_transport` prove
agreement with the interpreter's actual initializer execution, uniformly over
states. `source_meaning_load` includes initial immutable allocation, installation,
constructor dispatch and successful source/exports installation, including the
synthetic empty payable constructor when none is declared.

The proof chain is:

* `source_meaning_declaration_transport`: original declaration derivation plus
  actual body-phase success **implies** uniform code agreement.
* `source_meaning_module_transport`: lifts this through all declarations.
* `source_meaning_call_transport` / `source_meaning_load_transport`: equality of
  the complete interpreter API results, not only returned values.
* `source_meaning_compile_program`: composes with the public original-source
  compiler wrapper, retaining source identity, genuine checker and exact compiler
  equations for the same modules. The independent source module derivation is
  explicit; there is no opaque readiness predicate. Equality with the supplied
  nominal type environment is an explicit boundary, not an inferred trust claim.

The original load/constructor instance covers **one module, private scalar or
aggregate constants, and source-derived functions with covered bodies/defaults**.
The imported-dispatch extension below removes the single-module restriction for
ordinary nondeployment entry calls, not constructor/load execution. No theorem
claims a derivation for every accepted program. Public auto-getters, nested calls,
arbitrary nominal types and storage/immutable initializers need additional rules. No `supported_program` clauses were
removed and no backend preconditions were weakened.

`sourceMeaningCallTest` proves a source module with `N = 1 + 2` and
`f(x: uint256 = N): return x + N`. Actual external dispatch returns 6 with no
argument and 10 with argument 7; excess arguments reject. Default and explicit
constructors are transported, and the successful default constructor installs
`N = 3` in its runtime constant cell. `sourceMeaningCheckedTest` runs the public
source frontend/checker on this original syntax and connects its compiler wrapper
and runtime call theorem, conditional only on the existing raw compiler equation
for those exact checked declarations. It makes no bytecode-execution claim.

## General-policy modules and imported entry calls

`sourceMeaningPolicy` extracts independent finite constant dependencies from the
actual public `source_module_elaborate`, including imported dependency modules.
It also retains real linkage/export/override/signature/body evidence. The older
policy-free phase remains explicitly named `*_simple` and is not substituted for
public policy success.

`sourceMeaningPolicyDecl` interprets nonreentrancy defaults on source declaration
meanings, using original decorators, visibility and mutability. Pure functions
have no lock; explicit `reentrant` opts out of inherited external defaults.
`source_meaning_policy_program_transport` connects these meanings to actual
retained declarations. Its function/body derivation remains explicit: this is
**transport, not universal module completeness**. Declaration-only interface
modules are excluded from this executable-declaration theorem.

`sourceMeaningModules` proves module-independent lookup and ordinary imported
external invocation using the full module set and nominal environment. Selection
is through the independently source-derived declaration list; invocation does not
execute emitted body syntax to define its meaning. It includes defaults, argument
binding, locks, value checks, cast/errors/rollback and final pending deletions.
It does not establish nested internal/external call-expression meanings, getters,
or imported deployment/immutable initialization.

The three-module regression uses `base.N = 3`, `lib.A = base.N * 2`, main
`PAIR = (lib.A, [lib.A, lib.A + 1])`, and exported `lib.read`. It proves actual
policy-aware elaboration, independent dependency/declaration meanings, nested
aggregate return/global installation, and imported external return of 6.
A separate three-operand runtime Boolean test and an eager zero-divisor test
pin the distinct compile-time and runtime staging behaviors.

## Exact #543 witness inventory

The original `tests/sourceMeaningWitnessTestScript.sml` retains its frozen
37-input inventory: 36 accepted dependency environments, the pinned rejection
`method_id_var`, 21 pure single-return bodies and 19 bodies outside that smaller
relation. **Those 19 are no longer missing from independent source meaning**:
`tests/sourceMeaningLocationWitnessTestScript.sml` independently derives all
**40 original bodies**, including both constructors, and transports each actual
retained body at every initial state. It separately certifies original global/
parameter metadata and all 36 finite constant-dependency environments. These are
body counts, not 36 whole-program deployment/bytecode proofs. Both tests keep
fail-closed exact inventory guards.

Covered recursive returns: `pow_folded_exp.f`, `pow_negfold_base.f`, `fold_add.f`,
`fold_pow_lit.f`, `fold_cmp.f`, `fold_not.f`, `fold_shift.f`, `fold_minmax.f`,
`fold_powmod.f`, `fold_addmod.f`, `fold_abs.f`, `keccak_literal.f`,
`len_string_lit.f`, `method_id_b4.f`, `method_id_bytes.f`, `method_id_const.f`,
`neg_lit.f`, `pow_neglit_base.f`, `boolop_and3.f`, `c16_const_string_in_expr.f`,
and `c27_const_binop_fold.f`. A covered shift has a folded child; dynamic shifts
are still outside the general same-operand-type rule.

Former single-return gaps, now covered by the location-sensitive extension:
`enc_mid_const.f`, `enc_mid_methodid_call.f`, `enc_ensF_string_mid.f`,
`enc_ensF_uint_mid.f`, `enc_ensure_const.f`, `dec_unwrap_const.f`,
`ctl03_abi_method_id.foo`, `enc_ensT_uint_mid.f`, `lt_mixed_lit.f`,
`i12_immut_with_storage.f`, `p29_imm_multi.get`, `p29_imm_multi.who`, and
`p29_imm_multi.h`.
Former non-single-return gaps, also now covered: `method_id_storage.f`, `enc_mid_bytes4lit.f`,
`i12_immut_with_storage.__init__`, `p29_imm_multi.__init__`,
`rc09_abi_encode_data.foo`, and `rr03_abi.foo`.
Their new source derivations and complete body result/state equalities are
explicit kernel theorems, not acceptance-as-readiness premises. ABI capture,
delayed staging and runtime reference types are preserved. Broader #135 typing,
loops and external lowering obligations are still outside this fixed inventory.

## Validation

Run from the repository root (an isolated artifact directory avoids other agents'
project lock):

```sh
holbuild build sourceMeaningProgramTestTheory sourceMeaningCallTestTheory \
  sourceMeaningCheckedTestTheory sourceMeaningAggregateTestTheory \
  sourceMeaningExportTestTheory sourceMeaningWitnessTestTheory \
  sourceMeaningLocationTestTheory sourceMeaningLocationWitnessTestTheory \
  --skip-checkpoints --tactic-timeout 2.5
```

The test targets audit **every export of their sourceMeaning theories**, rejecting
open hypotheses, axioms, and oracle tags other than `DISK_THM` bookkeeping.
Kernel probes establish an independent derivation, successful elaboration and
all-state soundness of `x ** (1 + 2)`, eager invalid children, unbounded source
shifts, a resolved `raw_revert` source/build pair, its exact exception/state, and
conditional suppression of an unselected effect. No cheats are used.

The earlier expression-only receipt (90 exports / seven theories) is superseded
by the program-frontier audit in `sourceMeaningProgramTest`. Examples are split
across `sourceMeaningExampleDefs` and `sourceMeaningExample` to keep individual
proofs small. Every proof is checked at a 2.5-second tactic timeout.

Earlier body-entry forced audit (`--force=theory --skip-checkpoints --no-cache`) passed in
**39.720 seconds**, accepting **188 exports across 15 theories** with no CHEAT
warnings, axioms, open hypotheses, or non-`DISK_THM` oracle tags. This receipt
covers the program-frontier target and audits all imported sourceMeaning
exports; it does not force-rebuild or certify the entire backend dependency
closure. The aggregate test exceeds the preferred 30-second build budget
because it includes several program/module kernel-computation regressions.

The call-extension frontier was force-rebuilt without cache/checkpoints in two
batches; the second batch of thirteen theories passed in **291.883 seconds**.
The final current-revision three-root recheck passed at `--tactic-timeout 2.5`
with no cheats. Together the program/call/checked audits accept **287 exports
across 23 sourceMeaning theories**. The final root check after splitting a
borderline linking computation passed in **32.810 seconds** wall time; the
program test script itself took **6.6 seconds** and the call test **23.2 seconds**.
Receipts: `.agent-files/source-meaning-final-verified.log`,
`.agent-files/source-meaning-final-rest.log`, and the individual theory build
logs under `.agent-files/source-meaning-check/.holbuild/logs/current/vyper-hol/`.
These earlier receipts do not certify unrelated frontend/backend obligations.

The extension was rechecked against the latest shared ordinary expression/module
sources in an isolated project. Program/call, checked, aggregate and exported-call
roots passed; the full recursive witness inventory also passed, including its
kernel-closure audit. Final six-root build receipt:
`.agent-files/source-meaning-extension-combined-verified.log` (**282.913 seconds**,
unchanged targets reused; the inventory rebuilt). Earlier logs record initial
context-computation timeouts subsequently repaired using proved computed fields.
No cheats, new axioms or non-bookkeeping oracles are used. The witness inventory is intentionally much
slower than a small proof: it recomputes source contexts and independently proves
21 expressions and all-state bodies across all 37 fixtures.

The subsequent [location extension receipt](sourceMeaningLocation.md)
force-built all six new theories at 2.5 seconds and confirmed **36 dependency
environments / 40 original bodies / zero remaining**. All **37 sourceMeaning
theories / 828 exports** were kernel-tag audited (376 new exports and 452
unchanged legacy artifact exports). The latter is explicitly an artifact audit,
not a fresh build of the legacy backend dependency closure. Receipts:
`.agent-files/source-meaning-location-verified.log`,
`.agent-files/source-meaning-location-focused.log`, and
`.agent-files/source-meaning-location-legacy-audit.log`.

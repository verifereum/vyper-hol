# Source program/module elaboration (#135 extension)

`source_module_elaborate fuel trust policies keys program` is an executable opt-in HOL
phase. `program` is the pre-erasure `sourceSyntax` program, independent of
compiler folding metadata. The result is `SM_Ok (SourceRetained program modules)`
or an explicit `SM_Error`. No old JSON translator or metadata-backed retry is
reachable. Exhaustion and unsupported syntax are explicit errors.

Pipeline:

1. Validate the canonical source registry and its retained import edges.
2. Resolve all original constant initializers together (forward/imported names,
   duplicates, missing names and cycles use `sourceResolveModules/sourceConstEnv`).
3. Link retained exports/initializes/uses/implements namespaces and abstract
   overrides. Export expansion reuses the old syntax-only compact index
   algorithms, never its expression translator. Default compatibility compares
   canonical ORIGINAL trees, not evaluated values. Resolve source annotations
   and original bounds; elaborate declarations and function signatures.
4. Construct runtime module environments from those signatures. Add source
   parameters/locals lexically; elaborate constants, defaults, statement trees,
   constructor bodies, storage/immutable assignments, ranges and expressions.
5. Return the untouched source beside the runtime modules.

`source_module_check` checks exactly these modules with `check_contract T`.
In particular it checks constructors, unlike `check_contract F`.
`source_module_check_equations` exposes the exact phase equation, source retention
and checking equation. `source_module_link_program` and
`source_module_link_program_equations` expose the registry, constant dependency
result, exports and override links. `sourceModuleFrontendLib.elaborate` returns
an additional `linking` theorem, not a metadata-backed approximation. `sourceModuleFrontendLib.check` returns these equations,
the actual checker input and artifact; `elaborate_file` uses `sourceSyntaxLib`.
Use pre-erasure source JSON. Post-erasure annotated JSON has already lost
qualifiers and is not repaired using compiler `is_constant`/`is_immutable` flags.
The explicit [source-loader protocol](sourceModuleLoader.md) captures syntax
before that erasure; `elaborate_loaded`/`check_loaded` preserve both module policies.
`policies` is the key-aligned registry of `SourceModulePolicy nr_default declaration_only`.
Missing/misaligned entries reject. The original policy-free equations and ML input
record remain available as `source_module_elaborate_simple`/`check_simple` and
`sourceModuleFrontendLib.elaborate_simple`/`check_simple`; no policy is guessed.
The independent source-meaning/compiler statements continue to use these helpers.

`source_module_compile` additionally invokes the actual `compile_vyper` on the
same checked `tops` when the result is exactly `[(NONE,tops)]`.
`source_module_compile_equations` exposes that equality and the actual compiler
result. The current raw compiler API has no module-registry input, so this
wrapper explicitly reports `backend-module-linking` for multiple modules. It
never flattens imported namespace identities. This backend limitation does not
restrict module elaboration/checking.

## Explicit inherited boundary

`source_module_trust` carries canonical runtime module IDs, nominal identities,
nominal type definitions and storage slots. These are the remaining legacy
frontend import/layout/nominal-type trust, not source constant metadata. The
source registry must match the identity map exactly, runtime IDs must be unique,
and the first module must have ID `NONE`. Nominal identity entries must match
actual source declarations under those canonical module IDs, with unique keys.
Emitted nominal definitions must equal the inherited nominal environment. No constant value, array/string bound,
initializer, default, body or executable expression is a trust-record field.

Constructor and qualifier spellings are validated against their source scope;
unknown names are not dynamic names. Source annotations are canonicalized before
`source_type_resolve`, including bound-expression name resolution. Lexical
parameter/local contexts shadow module and builtin bindings. ABI intrinsics use
`SE_Intrinsic` identities, type arguments use `SE_Type`, and runtime variables
use `SE_Runtime`.

## Coverage and intentionally explicit incompleteness

`sourceModuleFrontendLibTestTheory` evaluates all 37 retained **whole source
programs** from `tests/fixtures/check_contract/source_syntax/`: all 36 valid
programs elaborate and check, and `method_id_var` rejects. Each successful row
exports an exact `_ast` equation and `_check`/`_composition` equations. Both
constructor-bearing witnesses are checked in deployment mode. Deleted/poisoned
folding fields decode to identical phase inputs. The tests also pin a complete
expected module for forward constants, defaults and local annotations.

`sourceModuleBoundaryTestTheory` pins complete imported-forward-reference and
source-bound/range ASTs, checks the imported module set, and rejects unknown
names. The mathematical bound `((1 << 256) >> 255) + 1` remains 3, not a wrapped
runtime result.

Source-only module linkage now resolves exports (including transitive
`__interface__`), module dependencies and override targets before body emission.
Overrides require initialized targets, unique links, compatible source signatures
and structural defaults; cycles are rejected. Abstract bodies never become
executable. Internal calls use source-derived signatures and linked targets.
External/static calls use source interface declarations, retain receiver/argument
and keyword evaluation order, and independently validate constant flags. Inline
interface casts and interface-annotated parameters/locals retain their source
interface descriptors even though their runtime type is address.

Preserved `.vyi` policy turns source function signatures into interface call
bindings, not executable stubs. Structs and other nominal declarations remain in
the imported module. Bodies must be the original ellipsis syntax; none is
fabricated or retried through legacy translation. Default nonreentrancy applies
to external non-pure functions, with `@reentrant` opt-out; internal/deploy functions
retain explicit policy. `sourceModulePolicyTestTheory` checks genuine captures
for imported interfaces, struct returns, interface-typed overrides, imported deployment and nonreentrancy.

This is still not the full legacy acceptance surface. JSON ABI interfaces and
omitted external default arguments are not connected to elaboration.
`implements` currently establishes namespace linkage, not full independent source
interface-obligation checking. Some assignment/iterator and expression forms
remain unsupported. Existing ordinary frontend APIs have **not** been switched;
no success/error path retries with the old expression translator.

Original declarations/defaults/imports remain in `SourceRetained`; structural
consumers never compare rewritten values. `sourceModuleLinkTestTheory` exercises
internal/imported and external calls, exports, initialized abstract overrides and
rejection of defaults with equal folded values but different original syntax.

These are executable-phase and compiler-composition equations, not a theorem
identifying source meaning with whatever the elaborator emits. No new source
operational semantics or universal source/runtime equivalence is claimed here.

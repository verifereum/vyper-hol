# Source program/module elaboration

Executable module APIs for pre-erasure `sourceSyntax` programs. See
[constant evaluation](constant-evaluation.md) for the canonical pipeline and
inherited trust boundary; [sourceModuleLoader](sourceModuleLoader.md) documents
source capture before qualifier erasure.

## API and equations

`source_module_elaborate fuel trust policies keys program` returns
`SM_Ok (SourceRetained program modules)` or an explicit `SM_Error`. It retains
the untouched source beside runtime modules. Exhaustion and unsupported syntax
are errors; no old JSON translator or metadata-backed retry is reachable.

`policies` is the key-aligned registry of
`SourceModulePolicy nr_default declaration_only`. Missing/misaligned entries
reject; no policy is guessed. The policy-free helpers are
`source_module_elaborate_simple`/`check_simple` and
`sourceModuleFrontendLib.elaborate_simple`/`check_simple`.

`source_module_check` applies `check_contract T` to exactly the elaborated
modules, including constructors. `source_module_check_equations` exposes the
phase, source-retention and checking equations.

`source_module_link_program` and `source_module_link_program_equations` expose
the registry, constant dependency result, exports and override links.
`sourceModuleFrontendLib.elaborate` returns a `linking` theorem;
`sourceModuleFrontendLib.check` returns the equations, actual checker input and
artifact. `elaborate_file` uses `sourceSyntaxLib`;
`elaborate_loaded`/`check_loaded` preserve both module policies. Inputs must be
pre-erasure source JSON: compiler `is_constant`/`is_immutable` flags do not repair
qualifiers lost from post-erasure annotated JSON.

`source_module_compile` invokes the actual `compile_vyper` on the same checked
`tops` only when modules are exactly `[(NONE,tops)]`.
`source_module_compile_equations` exposes that equality and the actual compiler
result. The raw compiler has no module-registry input, so multiple modules
produce `backend-module-linking`, never flattened namespace identities. This
backend limitation does not restrict module elaboration/checking.

## Shared interfaces

`sourceModuleSignature` owns declaration signatures and function contexts;
`sourceModuleContext` owns runtime signature contexts and policy-aware linkage.
Both the ordinary bridge and full-Source elaborator use these same constants.
`sourceModuleDecl` adds only body production, and `sourceModuleElaborate` composes
it with the shared contexts. The independent meaning theories use those same
shared contexts rather than redeclaring them.

## Resolution and source-sensitive rules

Constants resolve together, including forward/imported references. Annotations
and original bounds are canonicalized before `source_type_resolve`, including
bound-expression names. Constructor and qualifier spellings are checked in
source scope; unknown names are not dynamic names. Lexical parameters/locals
shadow module and builtin bindings. ABI intrinsics use `SE_Intrinsic`, type
arguments use `SE_Type`, and runtime variables use `SE_Runtime` identities.
Mathematical annotation bounds are not wrapped runtime arithmetic:
`((1 << 256) >> 255) + 1` is 3.

Linkage resolves exports (including transitive `__interface__`), module
dependencies and override targets before body emission. Export expansion reuses
syntax-only compact index algorithms, not the old expression translator.
Overrides require initialized targets, unique links, compatible source
signatures and structural defaults; cycles reject. Default compatibility
compares canonical original trees, not evaluated values. Original declarations,
defaults and imports remain in `SourceRetained`; abstract bodies never become
executable.

Internal calls use source-derived signatures and linked targets. External/static
calls use source interface declarations, retain receiver/argument and keyword
evaluation order, and independently validate constant flags. Inline interface
casts and interface-annotated parameters/locals retain source interface
descriptors even though their runtime type is address.

Preserved `.vyi` policy turns source function signatures into interface call
bindings, not executable stubs. Structs and other nominal declarations remain in
the imported module. Bodies must be original ellipsis syntax; none is fabricated.
Default nonreentrancy applies to external non-pure functions, with `@reentrant`
opt-out; internal/deploy functions retain explicit policy.

## Limits and regressions

JSON ABI interfaces and omitted external default arguments are not connected to
elaboration. `implements` establishes namespace linkage, not full independent
source interface-obligation checking. Some assignment/iterator and expression
forms remain unsupported. The ordinary frontend uses the separate hybrid
normalizer described in [constant-evaluation.md](constant-evaluation.md), not
this API's source-only body elaboration.

These executable-phase and compiler-composition equations do not identify source
meaning with whatever the elaborator emits. They are not a universal
source/runtime equivalence theorem.

- [sourceModuleFrontendLibTestScript.sml](sourceModuleFrontendLibTestScript.sml):
  exact AST/check/composition equations for original source fixtures, deployment
  checks, and independence from deleted/poisoned folding fields.
- [sourceModuleBoundaryTestScript.sml](sourceModuleBoundaryTestScript.sml):
  imported forward references, source bounds/ranges and unknown-name rejection.
- [sourceModuleLinkTestScript.sml](sourceModuleLinkTestScript.sml): calls, exports,
  initialized abstract overrides and rejection of structurally different defaults
  with equal folded values.
- [sourceModulePolicyTestScript.sml](sourceModulePolicyTestScript.sml): imported
  interfaces, struct returns, interface-typed overrides, imported deployment and
  nonreentrancy.

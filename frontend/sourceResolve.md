# Canonical source resolution

`sourceResolve`, `sourceResolveModules` and `sourceResolveProps` resolve retained
syntax for source elaboration and ordinary constant normalization. See [sourceSyntax.md](sourceSyntax.md),
[sourceModuleLoader.md](sourceModuleLoader.md) and
[constant-evaluation.md](constant-evaluation.md) for their input/trust boundaries.

## Checked integration API

* `source_resolve_program_registry program keys` associates exactly the retained
  `SourceProgram` modules, in order, with distinct source-loader namespace keys;
  success preserves the original module terms.
* `source_resolve_module_candidate registry owner source_expr` extracts
  `source_constant_candidate` and resolves it in the owning module's scope.
* `source_resolve_module_expr registry owner source_const_expr` handles the full
  unelaborated constant AST, ordered keywords and unsupported children included.
  Both expression APIs validate the registry first.
* `source_resolve_registry_constants registry` resolves original initializers
  in each module's lexical scope, then invokes `source_const_resolve []`.
  `source_resolve_program_constants` includes program/registry association.

Resolution failure is `NONE`, never `SCE_Dynamic` or a fabricated constant.
Success does not imply constant evaluation or source type acceptance: dynamic
initializers reach `SCEnv_NotConstant`, and unsupported functions/types remain
unsupported. Original annotation qualifiers, not `is_constant` metadata, select
constant declarations.

## Identity and lexical scope

Paths are component lists; member identities are `module_key ++ [name]`.
Kinds distinguish constants, dynamic bindings, functions, modules, nominal source
types, primitive bytes constructors, builtins and aliases. Only resolved modules
support member lookup. Alias chains end at canonical declaration paths; missing
targets and cycles fail closed.

`source_resolve_lexical` searches innermost scopes first. Once bound, a spelling
has no fallback even if its target is missing or noncallable. Checked module APIs
put the fixed builtin/primitive prelude last. Source declarations cannot mint
builtin identities. `Bytes[N]` / `bytesM` become `SCE_BytesType` only at an
`output_type` keyword after primitive-identity resolution. Primitive aliases work;
shadowing user types/dynamic bindings do not acquire that identity.

Low-level `source_resolve_expr scopes table position expr` and lookup helpers
are **not validators for arbitrary compiler-supplied tables**. Lexical consumers
must construct locals from retained arguments/block declarations.
`source_resolve_locals` / `source_resolve_local_bindings` create qualified dynamic
local entries; put them before enclosing scope/table entries.

Already tagged `SCE_Builtin` and `SCE_BytesType` inputs are rejected. Resolution
elaborates unelaborated syntax; it is not an idempotent output rewriter, and an
unvalidated resolution claim cannot authenticate itself.

## Module and metadata boundary

`SourceProgram` imports are anonymous. Loader namespaces cannot be recovered
from bodies, equal-body comparisons, source IDs, digest claims or
`resolved_path`. Obtain `keys` from an independent loading namespace and source
search rules, **not from trusted `import_infos`**. The relationship between that
namespace and physical files remains an explicit loader obligation.

Imports resolve from retained `SI_Import` / `SI_FromImport` syntax, including
aliases/relative levels. Missing targets, duplicate identities, reserved prelude
identities and constants without initializers reject. Imported constants are
evaluated from retained source, not compiler folded values.

`SourceImportClaim owner original_import target source_id` is redundant
evidence. `source_resolve_claims_ok` requires original-import membership,
syntax-derived canonical targets, registry membership, unique claim keys and
coverage of every import. Reusing one numeric ID for different canonical modules
rejects rather than merging them; equal bodies can still have distinct
identities. IDs are not used for resolution and this check does not authenticate
them. An adapter from `sourceSyntaxLib.import_claims` must obtain the independent
loader namespace and preserve original import associations; the claims alone
are insufficient.

## Theorems and reproduction

Lookup theorems establish canonical target membership and no residual aliases.
`source_resolve_builtin_identity` characterizes builtin elaboration;
`source_resolve_table_builtin_identity` prevents source-minted builtins. Bytes
descriptor theorems require primitive identities. `source_resolve_expr_names`
shows every remaining dependency is an actual supplied-table constant.
Declaration resolution preserves keys; program association preserves modules.
These are resolution contracts, not general statement typing/completeness.

```sh
holbuild build sourceResolveTestTheory --tactic-timeout 2.5
```

Regressions exercise shadowing, aliases/cycles, missing targets, primitive
identity, full/eager traversal, forged tags, imports/relative levels, duplicate
IDs/keys, equal-but-distinct bodies and constant-environment evaluation. Export
audits reject open hypotheses, axioms and nonstandard oracles.

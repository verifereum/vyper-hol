# Canonical source resolution (opt-in)

New theories: `sourceResolve`, `sourceResolveModules`, `sourceResolveProps`,
`sourceResolveTest`. Existing AST, evaluator, builtin and syntax files are
unchanged. No ordinary frontend entry point is redirected.

## Checked integration API

* `source_resolve_program_registry program keys` associates **exactly** the
  retained `SourceProgram` modules, in order, with distinct source-loader
  namespace keys. Successful association preserves the original module terms.
* `source_resolve_module_candidate registry owner source_expr` extracts
  `source_constant_candidate` and resolves it in that module's source scope.
* `source_resolve_module_expr registry owner source_const_expr` handles the
  entire unelaborated constant AST, including ordered keywords and all
  unsupported children. Both expression APIs validate the registry first.
* `source_resolve_registry_constants registry` resolves original constant
  initializers separately in each module's lexical scope, then invokes
  `source_const_resolve []`. `source_resolve_program_constants` combines this
  with the program/registry association.

An expression/registry resolution failure is `NONE`, never `SCE_Dynamic` or a
fabricated constant. Successful elaboration does not imply constant evaluation
or source type acceptance. In particular dynamic constant initializers reach
`SCEnv_NotConstant`, and unsupported functions/types stay explicitly unsupported.
The source constant annotation qualifier, not `is_constant` metadata, determines
which variable declarations supply constant initializers.

## Identity and lexical scopes

Paths are component lists. Module members have identity `module_key ++ [name]`.
Kinds distinguish constants, dynamic bindings, functions, modules, nominal
source types, primitive bytes constructors, builtins and aliases. Only resolved
modules support member lookup. Alias chains terminate at their target's
canonical declaration path; missing targets/cycles fail closed.

`source_resolve_lexical` searches scopes from innermost to outermost. Once a
spelling is bound there is no fallback, even when its target is missing or is
not callable. The checked module APIs put the fixed builtin/primitive prelude
last. Source declarations cannot create builtin identities. `Bytes[N]` and
`bytesM` become `SCE_BytesType` only at an `output_type` keyword and only after
resolving the primitive identity. Aliases work; user types and dynamic bindings
with the same spelling do not acquire a primitive identity.

The low-level `source_resolve_expr scopes table position expr` and lexical/table
helpers are reusable elaboration infrastructure, **not validators for arbitrary
compiler-supplied tables**. Future lexical consumers must construct local
bindings from retained source arguments/block declarations. `source_resolve_locals`
and `source_resolve_local_bindings` construct qualified dynamic local entries;
put their scope/table entries before the enclosing scopes/table. Function/default
scope construction and general statement typing remain future consumers.

Already tagged `SCE_Builtin` and `SCE_BytesType` inputs are rejected. This prevents
an unvalidated claim of prior resolution from being its own evidence; this is
an elaborator of unelaborated syntax, not an idempotent rewriter of its output.

## Modules and metadata boundary

`SourceProgram` deliberately has anonymous imported modules. Their actual loader
namespace cannot be recovered from their bodies, compiler source IDs, duplicate
body equality, digest claims or `resolved_path` metadata. The caller must obtain
`keys` from an independent source-loading namespace (including its source search
rules), **not construct it by trusting `import_infos`**. Establishing that loader's
relationship to physical files is an explicit future integration obligation.

Imports are resolved from retained `SI_Import` / `SI_FromImport` syntax against
that namespace, including aliases and relative levels. Missing targets,
duplicate module/declaration identities, reserved prelude identities and
constant declarations without initializers are rejected. Imported constants are
evaluated from their retained source, not seeded from compiler folded values.

`SourceImportClaim owner original_import target source_id` is redundant evidence.
`source_resolve_claims_ok` requires actual source import membership, the
syntax-derived canonical target, a present registry entry, unique claim keys,
and coverage of every retained import. If two claims reuse an ID for different
canonical modules they are rejected, **never merged**. Equal module bodies may
still have different identities. The numeric ID is not used by name resolution
and its authenticity is not claimed by this consistency check. An ML adapter for
`sourceSyntaxLib.import_claims` is intentionally not added: it must first obtain
the independent loader namespace and retain the original import association.

## Proofs and regressions

Lookup theorems establish canonical target membership and absence of residual
aliases. `source_resolve_builtin_identity` characterizes builtin elaboration;
`source_resolve_table_builtin_identity` shows source declarations cannot mint a
builtin. Bytes descriptor theorems require resolved primitive identities.
`source_resolve_expr_names` proves **every** remaining expression dependency is
an actual constant declaration in the supplied table. Declaration resolution
preserves identity keys; program association preserves all module terms.

Regressions cover missing names/targets, alias cycles/chains, canonical module
attributes, every shadowing kind, primitive aliases/shadowing, full expression
traversal, unsupported/eager children, forged resolved tags, source imports,
relative imports, duplicate IDs/keys, equal-but-distinct module bodies, actual
builtin lookup, and source-to-constant-environment evaluation. All four theories'
exports are audited for open hypotheses, axioms and nonstandard oracles.

Build with **holbuild 0.11.7**:

```sh
.agent-files/.holbuild-toolchain/bin/holbuild \
  frontend/sourceResolveTestScript.sml --tactic-timeout 2.5
```

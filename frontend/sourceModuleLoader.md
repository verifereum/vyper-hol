# Pre-erasure source-loader protocol

`tools/source_module_loader.py MANIFEST OUTPUT` uses pinned Vyper's
`PreParser` / `annotate_python_ast`, **before `get_node`**. It does not invoke
semantic analysis or folding. Qualifier calls, complete initializers, defaults,
decorators, imports and module declarations remain available to
[sourceSyntax.md](sourceSyntax.md). See
[constant-evaluation.md](constant-evaluation.md) for the cross-cutting trust model.

## Capture and protocol

The manifest supplies canonical namespace keys and dependency-first import order,
with the main module first, for example:

```json
[{"key":["main"],"path":"main.vy"},
 {"key":["lib"],"path":"lib.vy"}]
```

Run with supported Python and the pinned checkout:

```sh
PYTHONPATH=<VYPER_PIN-checkout> <python3.12> tools/source_module_loader.py manifest.json source.json
```

Output fields:

* `protocol`: `vyper-hol/source-loader-v1`
* `phase`: `annotate_python_ast-before-get_node`
* `vyper_pin`: pinned revision
* `annotated_ast`: original source syntax only
* `keys`: canonical keys in source order
* `nonreentrancy_by_default`, `declaration_only`: per-module policies
* `provenance`: diagnostic paths and source hashes

`sourceModuleLoaderLib.load_file` exposes syntax, namespace and policies
separately. `sourceModuleFrontendLib.elaborate_loaded` / `check_loaded` pass both
policies explicitly to HOL:

```sml
val source = sourceModuleLoaderLib.load_file "source.json";
val checked = sourceModuleFrontendLib.check_loaded
  {fuel=fuel, trust=trust, source=source} {layouts=layouts, address=address};
val source_equation = #equation (#elaboration checked);
val linking_equation = #linking (#elaboration checked);
```

## Trust and policy contracts

Ordinary annotated JSON is **not** a pre-erasure capture. Neither decoder nor
module elaboration reconstructs qualifiers from `is_constant`, `is_immutable`,
inferred types or folded values.

The loader, parser conversion, source-to-key association and policy claims are
**explicit trust inputs**. Protocol labels/hashes do not authenticate captures or
prove parsing correctness. `source_id` is not a canonical identity. HOL checks
the supplied registry/import edges, constant dependencies, nominal identities,
original bounds and executable phase; see [sourceResolve.md](sourceResolve.md).

`sourceModuleLoaderLib.policies` checks lengths and builds key-aligned
`SourceModulePolicy nr_default declaration_only` entries. HOL checks alignment
with the program registry. Declaration-only signatures supply external call
bindings, not fabricated runtime implementations of ellipsis bodies; nominal
declarations remain retained.

Default nonreentrancy applies only to non-pure external functions unless
`@reentrant` opts out. Callers must supply the inherited transient lock slot
`(NONE,"$.nonreentrant_key")`; missing slots reject. The loader does not fabricate
layouts or disable locking.

The policy-free semantic/compiler API is explicitly `*_simple`. Neither capture
nor a checking equation proves universal source semantics or bytecode behavior.

## Reproduction

```sh
holbuild build sourceModulePolicyTestTheory
```

This root exercises captures of imported interfaces, struct returns,
interface-typed overrides, imported constructors and nonreentrancy pragmas through
`Source.check_loaded_contract_result`. Loader policy claims remain trust inputs,
not authenticated metadata.

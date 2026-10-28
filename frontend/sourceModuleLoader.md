# Pre-erasure source-loader protocol

`tools/source_module_loader.py MANIFEST OUTPUT` runs the pinned Vyper
`PreParser`/`annotate_python_ast`, **before `get_node`**. It never calls semantic
analysis or the folder. It retains qualifier Calls, complete initializers,
function defaults, decorators, imports and module declarations.

The manifest supplies canonical source namespace identities and dependency-first
import order, e.g.:

```json
[{"key":["main"],"path":"main.vy"},
 {"key":["lib"],"path":"lib.vy"}]
```

Run with the supported Python and pinned checkout, for example:

```sh
PYTHONPATH=<VYPER_PIN-checkout> <python3.12> tools/source_module_loader.py manifest.json source.json
```

The output has:

- `protocol`: `vyper-hol/source-loader-v1`
- `phase`: `annotate_python_ast-before-get_node`
- pinned `vyper_pin`
- `annotated_ast`: original source syntax only
- `keys`: canonical module keys in source order
- `nonreentrancy_by_default`, `declaration_only`: per-module source-loader policies
- `provenance`: diagnostic paths and source hashes

`sourceModuleLoaderLib.load_file` decodes this protocol and exposes syntax,
namespace and policy terms separately. Pass that artifact to
`sourceModuleFrontendLib.elaborate_loaded` / `check_loaded`; these pass both
policies explicitly to HOL, rather than dropping or inferring them. For example:

```sml
val source = sourceModuleLoaderLib.load_file "source.json";
val checked = sourceModuleFrontendLib.check_loaded
  {fuel=fuel, trust=trust, source=source} {layouts=layouts, address=address};
val source_equation = #equation (#elaboration checked);
val linking_equation = #linking (#elaboration checked);
```

Ordinary annotated JSON is **not** a capture. Erased qualifiers cannot be recreated from compiler
`is_constant`/`is_immutable`/inferred-type/folded-value fields. Neither decoder nor
module elaboration uses such fields to reconstruct missing source.

The actual source loader, its parser conversion, source-to-key association and
policy claims remain an **explicit trust boundary**. Protocol labels and hashes
are claims, not authenticity or parsing-correctness theorems. `source_id` is not
a canonical module identity. HOL checks the resulting registry/import edges,
constant dependencies, nominal identities, original bounds and executable phase.

`sourceModuleLoaderLib.policies` validates list lengths and builds the explicit
key-aligned `SourceModulePolicy nr_default declaration_only` registry. HOL checks
alignment with the actual program registry. Declaration-only function signatures
supply external call bindings; ellipsis bodies are never fabricated into runtime
implementations, and nominal declarations are retained. Default nonreentrancy
applies only to non-pure external functions unless `@reentrant` opts out. The
caller must supply the inherited transient lock layout entry
`(NONE,"$.nonreentrant_key")`; checking still rejects a missing lock slot. The
loader never fabricates layouts or disables locking to make a check succeed.

`sourceModulePolicyTestTheory` exercises genuine captures of imported interfaces,
interface struct returns, interface-typed overrides, imported constructors and the nonreentrancy pragma
through the public `Source.check_loaded_contract_result` path. Captured policies
are source-loader trust inputs, not authenticated metadata. The policy-free
semantic/compiler API remains explicitly `_simple`; neither these captures nor
their checking equations claim a universal source operational-equivalence proof.

# Original source syntax retention

`sourceSyntaxTheory` / `sourceSyntaxLib` retain the original program used by
source elaboration and paired ordinary normalization. They are separate from
the metadata-consuming legacy `jsonASTLib` decoder.
See [constant-evaluation.md](constant-evaluation.md) for the cross-cutting design
and trust boundary.

## API

```sml
JSONDecode.decode sourceSyntaxLib.annotated_ast json
JSONDecode.decode sourceSyntaxLib.annotated_ast_with_provenance json
```

The first returns a HOL `SourceProgram main imports`; the second returns
`{syntax, provenance, import_claims}`. The input envelope is `{ast, imports}`;
`wrapped_annotated_ast` also accepts an `annotated_ast` envelope. `expression`,
`statement`, `declaration` and `source_module` are reusable component decoders.
There is **no fallback to the ordinary decoder/translator**.

Syntax retains literals, arbitrary attribute receivers, subscripts, operators,
aggregates/dictionaries, conditionals, ordered call keywords, external/static
calls and named dependency bindings. Statements/declarations retain
initializers, defaults, annotations, decorators, imports, exports, uses and
initializes. Ranges retain the complete iterator call, including runtime
operands and the original `bound`, rather than a computed number.

Annotations reuse `sourceConstAnnotation` for nested bounds, HashMaps and
qualifiers. Missing/null optional annotations become `NONE`; required ones
reject missing/null. A malformed **present** annotation fails without
inferred-type or folded-literal fallback.

`source_constant_candidate` structurally extracts a constant candidate. It does
not resolve calls by spelling or fabricate constants for unsupported general
expressions: these become `SCE_Unsupported` with their children. The original
general expression remains in the program.

## Pre-erasure capture boundary

Pinned Vyper's `vy_ast.get_node` erases `constant(...)` / `immutable(...)`
qualifier calls into plain annotations plus detached flags. This occurs in
`parse_to_ast`, **before semantic analysis**, so ordinary annotated JSON cannot
recover the original qualifiers. This decoder never invents them from flags.

Opt-in callers must capture syntax before erasure. The pinned `PreParser` /
`annotate_python_ast` boundary is demonstrated by
`tests/fixtures/check_contract/source_syntax/generate.py` and exposed by
[sourceModuleLoader.md](sourceModuleLoader.md). Capture does not invoke semantic
analysis, constant folding or bytecode generation. Parser lexical normalization
(e.g. negative integer literals) still occurs: this is AST retention, not a
concrete-token parser correctness theorem. Ordinary frontend integration must
obtain pre-erasure syntax, not reconstruct it from compiler metadata.

## Provenance and structural consumers

Provenance separately records JSON structural paths, node/source IDs, `src`,
line/column ranges, module paths and digest claims. `import_infos` mappings are
also separate from original import syntax. These claims are **unvalidated**, not
canonical identities; [sourceResolve.md](sourceResolve.md) describes resolution.
Inferred types/folded values enter neither semantic terms nor provenance
traversal. This layer does not validate settings/pragmas, general typing or
linking.

`SourceRetained original executable` preserves originals alongside executable
payloads. `source_structural_imports` / `source_structural_defaults` read only
original syntax; executable-replacement theorems preserve both views. Structural
default comparison distinguishes `1+2` from `3`, even when values agree. Consumers
must retain original views until structural comparisons and resolution finish;
ordinary legacy consumers are not redirected by this API.

## Reproduction and evidence limits

`sourceSyntaxLibTestScript.sml` requires metadata-independent decoding of the
37 retained witness sources, including source-invalid `method_id_var`, and
annotated JSON fixtures. It compares originals with deleted and recursively
poisoned folded/type/flag/source-ID metadata; erased qualifiers remain erased.
Tests also exercise annotation positions, ranges, imports/aliases, defaults,
attributes, provenance and malformed annotations that folded metadata must not
rescue. Theorem tag checks reject nonstandard oracles.

With a pinned checkout and supported Python environment:

```sh
PYTHONPATH=<VYPER_PIN-checkout> <python3.12> \
  tests/fixtures/check_contract/source_syntax/generate.py --check
holbuild build sourceSyntaxLibTestTheory sourceConstASTLibTestTheory
```

The fixture manifest records source SHA256 claims and the parser boundary.
Decoding establishes **neither evaluator acceptance, reification, checking,
parity, behavior nor ordinary-frontend integration**. Successful decoding of
`method_id_var` is intentional; required-constant consumption must reject its
runtime string operand.

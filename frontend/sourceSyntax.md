# Opt-in original source syntax retention (#543)

`sourceSyntaxTheory` / `sourceSyntaxLib` are **separate from the ordinary
frontend**. Neither `jsonASTLib` nor the ordinary translators/checker entry
points were changed or redirected to the incomplete constant evaluator.

## API

```sml
JSONDecode.decode sourceSyntaxLib.annotated_ast json
JSONDecode.decode sourceSyntaxLib.annotated_ast_with_provenance json
```

The first returns a HOL `SourceProgram main imports` term. The second returns
`{syntax, provenance, import_claims}`. The input envelope is `{ast, imports}`;
`wrapped_annotated_ast` additionally accepts an `annotated_ast` envelope.
`expression`, `statement`, `declaration`, and `source_module` are reusable
component decoders. There is **no retry of the ordinary decoder/translator**.

Semantic source syntax contains literals, arbitrary attribute receivers,
subscripts, unary/binary/Boolean/comparison forms, aggregates/dictionaries,
conditionals, calls including ordered keywords, external/static calls, and
named dependency bindings. Statements/declarations retain initializer/default
expressions, declaration annotations, decorators, imports, exports, uses and
initializes. A range is the complete original iterator call, including runtime
operands and the original `bound` expression; it is never reduced to a number.
Annotations reuse `sourceConstAnnotation` for nested bounds, HashMaps and
qualifiers. Missing/null optional annotations are explicit `NONE`; required
annotations reject missing/null. Any malformed **present** annotation fails;
there is no inferred-type or folded-literal fallback.

`source_constant_candidate` is a HOL structural extraction function. It does
not resolve calls by spelling or accept general expressions merely because
constant evaluation is incomplete. General-only constructs become explicit
`SCE_Unsupported` candidates with their children, not fabricated constants.
The general expression remains available in the original program.

## Important upstream erasure boundary

Pinned Vyper's `vy_ast.get_node` erases declaration qualifier calls such as
`constant(uint256)` and `immutable(uint256)`, replacing their annotations with
`uint256` and detached `is_constant` / `is_immutable` flags. This already occurs
in `parse_to_ast`, **before semantic analysis**, not only during folding.
Consequently the ordinary annotated JSON cannot recover this original syntax.
This library does **not** invent qualifiers from those flags. It can decode
ordinary JSON's retained syntax, but that alone is not full source retention.

To retain qualifiers, the opt-in caller supplies JSON captured before this
erasure. `tests/fixtures/check_contract/source_syntax/generate.py` demonstrates
that boundary using the pinned `PreParser` and `annotate_python_ast`, before
`vy_ast.get_node`; it serializes to the same source node field conventions.
It never invokes semantic analysis, the constant folder or bytecode generation.
The parser still performs its ordinary lexical normalization (e.g. `-5` to an
Int node). This is AST retention, not a concrete-token parser correctness proof.
New ordinary frontend integration must obtain the pre-erasure syntax rather
than attempting to reconstruct it from compiler qualifier flags.

## Provenance and structural consumers

Provenance records the JSON structural path, node/source IDs, `src`, line/column
ranges, module paths and source digest claims separately. Import mapping claims
(`import_infos`) are retained separately from original import syntax. These
IDs, paths, digests and mappings are **unvalidated**, not canonical module or
declaration identities. A resolver must validate them. No inferred type or
folded value enters the semantic terms, and those fields are not traversed for
provenance. Settings/pragma validation, general source typing and linking are
not implemented here.

`SourceRetained original executable` keeps immutable originals beside any
executable payload. `source_structural_imports` and `source_structural_defaults`
read only the original. Theorems show executable replacement preserves both
views. The regression deliberately distinguishes source defaults `1+2` and
`3`; it does not substitute value equality for default-override comparison.
Actual legacy structural consumers remain unchanged; future opt-in consumers
must use these original views until structural comparisons/resolution finish.

## Tests and evidence limits

`sourceSyntaxLibTestScript.sml` checks all **37** retained witness sources,
including source-invalid `method_id_var`, against explicit original syntax
subtrees. Each is decoded unchanged, with folded/type metadata deleted, and
with recursively injected different well-formed Int/Bool folded literals and
poisoned inferred types, flags and source-ID claims. Semantic terms must be
identical. All 36 historical annotated JSON fixtures also pass the same
metadata-independence comparison (their erased qualifiers remain erased).

Additional tests cover range bounds/runtime operands, nested HashMap bounds,
qualifiers and annotations in argument/return/local/loop/struct/event/interface
positions; imported modules/aliases/named initializes bindings; structural
defaults; arbitrary attributes/conditionals/external calls; provenance; and
malformed present annotations that usable folded metadata must not rescue.
The tests audit new theorem tags for nonstandard oracles.

Reproduce fixture/source correspondence (requires the pinned Python checkout):

```sh
PYTHONPATH=/home/lukasz/vyper \
  /home/lukasz/.local/share/uv/tools/vyper/bin/python \
  tests/fixtures/check_contract/source_syntax/generate.py --check
.agent-files/.holbuild-toolchain/bin/holbuild \
  frontend/sourceSyntaxLibTestScript.sml frontend/sourceConstASTLibTestScript.sml
```

Use **holbuild 0.11.7**. The fixture provenance manifest records all 37 source
SHA256s and the parser boundary. The tests establish decoding/retention only:
**no source evaluator acceptance, reification, checking, parity, behavior,
ordinary-frontend integration or whitelist removal follows from a decode**.
In particular, successful decoding of `method_id_var` is intentional; its later
required-constant consumer must reject the runtime string operand.

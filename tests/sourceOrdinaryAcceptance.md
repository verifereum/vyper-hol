# Ordinary frontend regressions

The ordinary frontend uses a paired hybrid bridge: source constants and required
parameters are computed from original syntax, while residual runtime
type/import/layout claims remain inherited. See
[`frontend/constant-evaluation.md`](../frontend/constant-evaluation.md) for the
trust boundary. These finite regressions do not establish full-language
acceptance, independent inference or unrestricted backend correctness.

## Regression purpose

`sourceOrdinaryProgramInventoryTestTheory` exercises the 26 retained cases in
`sourceOrdinaryFixtureLib.rows` through the ordinary public API:

- Complete runtime ASTs and checker artifacts are compared with independent
  legacy-fixture expectations, including decimal, initializer and interface cases.
- Deleting or poisoning folded fields must leave complete normalized modules,
  artifacts, checker equations and composition equations unchanged.
- Pairing, phase, retained-source and deployment-check equations are audited for
  kernel closure.
- `simple`, `imported_struct` and `duplicate_interface` additionally compare
  `prepare_check_input`, scalar `check_contract`, and both two-file wrappers.

The public record input is `sourceOrdinaryProgramLib.input`; file wrappers take
original and annotated paths plus explicit inherited claims. Annotated-only
compatibility uses explicit `*_legacy` names. There is no Source-failure retry
through legacy translation.

The independent full-Source acceptance/semantic suites are extracted with the
optional feature. Shared inventory, trust and expected-AST utilities live in
`sourceOrdinaryFixtureLib`; ordinary tests do not load a full-Source library.
Whole-program witnesses compare exact modules against independent legacy
signature/statement skeletons plus the explicit expected expressions in
`sourceExprWitnessDefs.source_expr_witnesses` (including separately pinned
constructor folds), check those expected modules, and retain delete/poison
invariance. Raw legacy residual MethodId is not claimed to pass checking.
`sourceOrdinaryProgramParityTest` compares nine checked deploy/runtime byte
pairs, including the two Boolean-chain witnesses, against pinned Python output.
`sourceBytecodeFixtureLib` supplies only common fixtures/layouts/trust/expected
bytes and kernel-audit utilities, not full-Source phase certificates.

## Fixture provenance

`sourceOrdinaryPin.py` inventories the retained HOL cases and five additional
pin/capture-only cases: `attribute_initializes`, `nested_initializes`,
`imported_constants`, `interface_struct` and `relative_uses`. These additional
pairs live in `fixtures/check_contract/source_ordinary/pin_only/`; they are not
additional elaboration, kernel-checking or backend certificates. The audit
rejects missing or newly unlisted upstream fixtures. The separate `source_syntax`
and `source_loader` suites are not substitutes for this inventory.

Original captures in `fixtures/check_contract/source_ordinary/` precede
`get_node`, semantic analysis, folding and qualifier erasure. Their counterparts
in `source_ordinary/annotated/` come from the same pinned source bytes and
source-ID registry. Existing legacy fixtures remain independent expectations;
they are not rewritten by pair generation.

`INHERITED_SOURCE_IDS` is an explicit inherited namespace map, not compiler
traversal order or inferred source identity. Retained `inherited_origins` binds
canonical keys, paths, SHA-256, compiler source IDs and runtime module IDs.
Imports are selected by resolved path and hash; unexpected or missing imports
fail. Repeated aliases are deduplicated only for identical complete module
claims at the same path/hash/ID. In particular, `duplicate_interface` retains
source ID 1 and inherited HOL identity `SOME 3` (source ID + 2).

Pairing requires exact declaration node IDs and module source IDs; missing
bodies or mismatched definitions are not patched. Decimal/scientific spellings
may differ only with exact value equality and valid precision, retaining original
tokens. `Bytes[INF]` is confined to matched `msg.data` metadata. Imported flags
retain canonical qualified identity. None of these rules trusts executable
folded values or substitutes source syntax.

At `VYPER_PIN`, `abi_encode`, `interface_struct_return` and `daddy` require
explicit pragma-only `0.5.0a3` → `0.5.0a4` adaptations. Adapted acceptance is not
acceptance of the original source.

## Reproduction

Run from the repository root with an isolated environment for the compiler
revision in `VYPER_PIN`:

```sh
PYTHONPATH=.agent-files/folded-value-validation/vyper-src \
  .agent-files/folded-value-validation/venv/bin/python tests/sourceOrdinaryPin.py
python tests/sourceOrdinaryPinTest.py
holbuild -j1 --maxheap 6000 build \
  sourceOrdinaryProgramInventoryTestTheory sourceOrdinaryProgramParityTestTheory \
  --tactic-timeout 2.5 --skip-checkpoints
```

Add `--generate` to the pin command only when intentionally refreshing retained
pairs. The generator checks imported compiler implementation bytes against
`VYPER_PIN` and checks the explicit identity map against independent legacy
evidence. Bytecode parity uses retained `lowering/defs/bytecode/folded-value-oracle`
fixtures and the unchanged backend. Exact computation on this finite inventory
is not universal compiler correctness.

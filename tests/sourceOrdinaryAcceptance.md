# Ordinary frontend regressions

The ordinary frontend uses a paired hybrid bridge: source constants and required
parameters are computed from original syntax, while residual runtime
type/import/layout claims remain inherited. See
[`frontend/constant-evaluation.md`](../frontend/constant-evaluation.md) for the
trust boundary. These finite regressions do not establish full-language
acceptance, independent inference or unrestricted backend correctness.

## Regression purpose

`sourceOrdinaryProgramInventoryTestTheory` exercises the 27 retained cases in
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

Shared inventory, trust and expected-AST utilities live in
`sourceOrdinaryFixtureLib`; ordinary tests do not use the full-Source acceptance
library or elaborator as their expected-body oracle.
Whole-program witnesses compare exact modules against independent legacy
signature/statement skeletons plus the explicit expected expressions in
`sourceExprWitnessDefs.source_expr_witnesses` (including separately pinned
constructor folds), check those expected modules, and retain delete/poison
invariance. Raw legacy residual MethodId is not claimed to pass checking.
`sourceOrdinaryProgramParityTest` compares nine checked deploy/runtime byte
pairs, including the two Boolean-chain witnesses, against pinned Python output,
exporting each `*_exact_checked_backend` equation. `sourceLegacyCompatibilityTest`
independently decodes the seven raw legacy fixtures and certifies explicit
runtime/deploy checker outcomes with `EVAL (mk_check_contract input)` followed
by logical simplification of determined ABI-size existentials:
`fold_add`, `fold_cmp`, `enc_mid_const`, `fold_powmod`, `fold_addmod` and `fold_abs`
accept; `pow_folded_exp` rejects in both modes. Its `x ** (1 + 2)` requires source
normalization before checked exponentiation; removed folded-value trust is not
restored. Positive and negative equations are saved by name, and the six accepted
fixtures additionally require closed raw backend compilation equations (`SOME`
actual deployment and runtime byte lists). No raw compilation claim is made for
`pow_folded_exp`. It reuses an ordinary backend certificate only when the
complete compile left-hand side is identical; otherwise it evaluates the fresh
legacy AST directly, without oracle rewrite rules. The `fold_add` legacy backend
input is explicitly required and proved to differ from the ordinary normalized
input: annotated-only legacy APIs may retain original arithmetic, so their bytes
need not match the pin. These compatibility certificates do not claim legacy
semantic correctness or extend generic folded-value trust.
`sourceBytecodeFixtureLib` also checks the 37 distinct source names, exact source
directory inventory, `@external` entry points, and the fixed seven compatibility
names and manifest membership. Source/oracle fixtures and provenance remain unchanged.
`sourceOrdinaryAudit.sml` rechecks all 27 ordinary cases, 36 whole-program witness
inventories and kernel closure on cache hits, reopens legacy raw compilation
equations against fresh legacy ASTs and requires `SOME` actual bytes for the six
accepted cases, checks all seven runtime/deploy outcomes against the explicit
per-case expectations (never inferred from actual results), and rechecks the
`fold_add` input distinction. It also checks the nine ordinary exact backend
statements against the retained checked artifacts and pinned bytes, reporting
baseline lowering admissions separately.

## Separate full-Source scope

`sourceOrdinaryAcceptanceTestTheory` checks the original 26 cases through
`Source.check_loaded_contract_result`, using `sourceOrdinaryAcceptanceLib.rows`
and explicit full-source body and signature expectations. It filters only
`address_bytes32` from the shared 27-case inventory: those wide runtime
conversions remain ordinary inherited claims, not full-Source inference.
This separate suite is not the hybrid bridge's residual-body oracle.
`sourceOrdinaryProgramMeaningTest` links body and compile/body certificates;
`sourceMeaningWitnessTest` and `sourceMeaningLocationWitnessTest` retain the
independent staged-meaning and location-sensitive witnesses. Their supported-body
scope, independent-derivation and context premises still apply.

## Fixture provenance

`sourceOrdinaryPin.py` inventories exactly 32 upstream fixtures: 27 ordinary
cases and five pin/capture-only cases. `address_bytes32` has explicit expected
ASTs for address-to-bytes32, address-to-bytes21 and bytes20-to-bytes32, with
complete module/artifact and delete/poison checks. These are inherited ordinary
runtime conversion parents, not independently inferred Source conversions.
The separate whole-program inventory contains 36 valid witnesses.

The inventory also includes five additional
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
`address_bytes32` explicitly retains source ID 0 and main identity `NONE`,
checked against its independent legacy fixture. Legacy paths may be fixture-relative
or carry the exact sanitized `./tests/fixtures/check_contract/` prefix; source
identity is never selected by basename alone.

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
  sourceOrdinaryProgramInventoryTestTheory sourceLegacyCompatibilityTestTheory \
  sourceModuleParityTheory sourceOrdinaryAcceptanceTestTheory \
  sourceMeaningWitnessTestTheory sourceMeaningLocationWitnessTestTheory \
  sourceOrdinaryProgramMeaningTestTheory \
  vyperCheckContractFrontendLibTestTheory vyperCheckContractLibTestTheory \
  vyperTypeBuiltinsTheory vyperTypeContractSoundnessTheory \
  supportedExprFormPropsTheory vyperLoweringCorrectTheory \
  --tactic-timeout 2.5 --skip-checkpoints
holbuild -j1 --maxheap 6000 run tests/sourceOrdinaryAudit.sml
```

Add `--generate` to the pin command only when intentionally refreshing retained
pairs. The generator checks imported compiler implementation bytes against
`VYPER_PIN` and checks the explicit identity map against independent legacy
evidence. Ordinary bytecode parity uses retained
`lowering/defs/bytecode/folded-value-oracle` fixtures and the unchanged backend;
legacy compatibility checks six positive raw compilations and seven explicit
positive/negative checker boundaries, not oracle parity.
See [source-module parity](sourceModuleParity.md) for the separate bytecode
comparison workflow. Exact computation on this finite inventory is not
universal compiler correctness.

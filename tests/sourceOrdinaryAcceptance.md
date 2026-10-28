# Ordinary frontend acceptance inventories

Two distinct finite gates are retained. Neither is a full-language acceptance,
independent inference or backend-correctness claim.

## Current clean ordinary gate

The general public names now use the paired hybrid bridge in
[`frontend/sourceOrdinaryBridge.md`](../frontend/sourceOrdinaryBridge.md).
`prepare_check_input`, `check_contract_result` and `check_contract` take
`sourceOrdinaryProgramLib.input`; file variants take original and annotated
paths plus explicit inherited claims. Annotated-only compatibility is available
under explicit `*_legacy` names. There is no Source-failure → legacy retry.
`Source.*` remains a separate full-Source interface, not the ordinary bridge.

`sourceOrdinaryProgramInventoryTestTheory` audits **26 retained ordinary cases**:
complete expected ASTs, independent checker artifacts, fold deletion/poisoning,
pairing/source/phase/deployment equations and selected record/scalar/two-file
wrapper agreements. See [the detailed inventory](sourceOrdinaryProgramInventory.md).
Runtime type/import/layout claims on residual nodes remain inherited. Source
constant values and required #543 parameters are computed from original syntax.

Current receipts:

| Gate | Result / receipt |
|---|---|
| Ordinary inventory | 26/26 PASS; `.agent-files/receipts/decimal-inventory-final25.log` is a cached successful completion. |
| Whole retained witnesses | 36/36 valid ordinary witnesses built; exact AST/artifact equality with the tested Source results, plus delete/poison invariance. `.agent-files/issue543-ordinary-final-validation.log` records inventory and witness targets built; the command later timed out at parity. |
| Ordinary exact bytecode parity | 9/9 certificates; separate successful `.agent-files/issue543-ordinary-parity-final.log`, 186.850s. |

All 36 witness ASTs are identical to the existing Source ASTs. The independent
40-original-body meaning coverage keeps its existing scope and context premises;
this is not a new universal call/deployment theorem.
`sourceOrdinaryProgramMeaningTest` exports 40 linked body certificates and nine
actual compile/body compositions. Forced proof builds and final scoped export /
combined regression audits pass; see `docs/ISSUE_543_IMPLEMENTATION_STATUS.md`.
The external matrix stays **32 matches / 4 failures / 1 expected rejection**,
not a global green build.

## Pinned captures and reproduction

`sourceOrdinaryPin.py` inventories 31 main cases and 49 source modules including
imports: the 26 retained HOL cases (35 modules), plus five pin/capture-only
upstream cases (14 modules): `attribute_initializes`, `nested_initializes`,
`imported_constants`, `interface_struct`, and `relative_uses`. The latter pairs
live under `fixtures/check_contract/source_ordinary/pin_only/`; they are **not**
additional source elaboration, kernel-checking, or backend certificates.
The audit rejects missing or newly unlisted upstream fixtures rather than
silently excluding them. Separate `source_syntax` and `source_loader` suites
are not substitutes.

```sh
PYTHONPATH=.agent-files/folded-value-validation/vyper-src \
  .agent-files/folded-value-validation/venv/bin/python tests/sourceOrdinaryPin.py --generate
python tests/sourceOrdinaryPinTest.py
holbuild -j1 --max-heap 6000 build sourceOrdinaryProgramInventoryTestTheory \
  --tactic-timeout 2.5 --skip-checkpoints
```

Omit `--generate` to verify retained pairs without rewriting. The generator
requires the authoritative `VYPER_PIN` and checks imported compiler implementation
bytes. Original captures precede `get_node`, analysis, folding and qualifier
erasure; annotated claims are generated from the same input bytes/ID registry.
Independent legacy fixture ASTs are not rewritten. Regenerated pairs match all
31 cases; `.agent-files/source-ordinary-pin.json` retains source hashes/results
and labels retained-HOL-gate versus pin-only scope.

The duplicate-interface upstream fixture retains source ID **1**, including both
identical aliases, so its explicit inherited HOL module identity is **SOME 3**
(source ID + 2), not the old `SOME 5`. The independent SML oracle, source capture,
and annotated pair agree on that identity. The generator checks the explicit ID
map against retained legacy evidence for this case and the new upstream cases;
it never derives the trust map from its own compiler run. Duplicate aliases still
require identical full module claims at the same path/hash/ID; divergent aliases
are rejected.

At pin `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`, decimals enabled,
23 retained originals and all five pin-only originals accept. `abi_encode`,
`interface_struct_return` and `daddy` have
original `VersionException`; pragma-only `0.5.0a3` → `0.5.0a4` adaptations accept.
Adapted acceptance is not acceptance of the original source.

Decimal canonicalization checks exact value while retaining original syntax;
`INF` is confined to matched `msg.data` metadata. Imported flags retain canonical
qualified identity. None of these exceptions permits replacement source syntax
or executable folded-value trust.

## Earlier full-Source acceptance gate (retained regression)

`sourceOrdinaryAcceptanceTestTheory` separately checks the 26 cases through
`Source.check_loaded_contract_result`. Its 130 exported certificates are
kernel-closed (`ORDINARY_ALL_26_KERNEL_CLOSED`); historical receipts are
`.agent-files/source-ordinary-main-{Core,Expr,Modules,Daddy,Acceptance}.log`.
It checks full source-derived bodies and signatures against explicit expectations,
with documented constant/decimal/interface differences from legacy. The clean
hybrid bridge has its own exact residual-body expectations; do not conflate them.

The earlier `.agent-files/source-ordinary-main-validation5.log` is an 18-target
snapshot receipt, not a fresh combined validation. `Source.artifact_semantics`
remains conditional extraction, not automatic semantics for every ordinary
policy/import case. Broader language, inference and backend work remain outside
this verified scoped switch; final receipts do not certify unrestricted backend
correctness or full #135 inference.

# Current clean ordinary bridge: 26-case gate

`sourceOrdinaryProgramInventoryTestTheory` audits the **clean ordinary** public
API, not the older full-Source acceptance inventory. Its five owner theories
exercise all 26 names in `sourceOrdinaryAcceptanceLib.rows`. Each row checks:

- the exact complete runtime AST against the independent legacy-fixture
  expectation (including its documented decimal/initializer/interface cases);
- the checker artifact against the independent legacy checker;
- deletion and malformed poisoning of all folded fields through
  `check_contract_result`, comparing complete normalized modules, artifacts,
  checker equations and composition equations, not merely parsed claims;
- kernel-closed pairing, phase, retained-source and deployment-check equations.

`simple`, `imported_struct` and `duplicate_interface` additionally compare
`prepare_check_input`, scalar `check_contract`, `check_contract_file_result` and
scalar `check_contract_file`. Both the record and two-file public routes are
therefore tested with imported and duplicate-interface identities.

## Pinned pair generation

```sh
PYTHONPATH=.agent-files/folded-value-validation/vyper-src \
  .agent-files/folded-value-validation/venv/bin/python tests/sourceOrdinaryPin.py --generate
python tests/sourceOrdinaryPinTest.py
holbuild -j1 --maxheap 6000 build sourceOrdinaryProgramInventoryTestTheory \
  --tactic-timeout 2.5 --skip-checkpoints
```

Omit `--generate` to check both retained sides without rewriting. Captures in
`fixtures/check_contract/source_ordinary/<name>.json` retain pre-`get_node`
qualifiers. Corresponding compiler output is in `source_ordinary/annotated/`.
Both are generated from the **same pinned input bytes and source-ID registry**.
The existing ordinary fixtures remain untouched as independent expected runtime
AST/layout/type/ID claims. Pragma-only adaptations remain explicitly recorded;
they are not original-source acceptance.

`INHERITED_SOURCE_IDS` is an explicit inherited namespace map, not inferred
from syntax or compiler traversal order. The pinned compiler input bundle is
seeded by actual resolved source paths. The retained `inherited_origins` binds
canonical keys, paths, SHA-256, compiler source IDs and inherited runtime module
IDs. HOL tests check this map against independently expected legacy IDs.
Compiler import output is selected/ordered by resolved path **and hash**.
Unexpected or missing imports fail. Repeated interface aliases are deduplicated
only when the entire module object is identical at the same path/hash/ID,
including declarations and claims. Divergent same-source declarations fail;
there is no generic relaxed pairing rule.

`sourceOrdinaryClaimsLib.pair_program` receives the unwrapped genuine original
capture, enforces exact declaration node IDs and module source IDs, and retains
original qualifier roots. No stale node IDs, missing bodies or mismatched
definitions are patched or ignored. Decimal/scientific spellings may differ
only with exact value equality and valid precision; original tokens are retained.
`Bytes[INF]` is restricted to matched original `msg.data` metadata. Imported flag
claims use canonical qualified identity, not a new inference rule.

The generator's six identity/order/duplicate tests pass; regenerated pairs match
all 26 cases. The aggregate audits `BRIDGE_ALL_26_KERNEL_CLOSED`; its successful
cached completion is `.agent-files/receipts/decimal-inventory-final25.log` (not fresh proof execution).
`.agent-files/issue543-ordinary-final-validation.log` also records the inventory
and all 36 whole-witness targets built. That command later timed out at parity;
the separate `.agent-files/issue543-ordinary-parity-final.log` succeeds in
186.850s for nine deploy/runtime certificates.

The 36 witnesses compare ordinary modules/artifacts exactly to the tested Source
results, retaining the existing independent 40-body meaning scope and context
premises. `sourceOrdinaryProgramMeaningTest` exports 40 linked body and nine
actual compile/body certificates. Final forced builds, scoped export audits and
combined regressions pass; receipts are in the implementation-status report.
No full #135/general-builtin coverage or unrestricted backend-correctness claim
is implied. The wider matrix remains 32 matches / 4 external failures / one
expected rejection, not global green.

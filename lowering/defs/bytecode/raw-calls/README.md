# raw_call witnesses

These sources exercise the lowering of `raw_call`
([issue #554](https://github.com/verifereum/vyper-hol/issues/554)): byte-string
data in statement and expression position, `max_outsize`, `is_static_call`,
`is_delegate_call`, `revert_on_failure=False` with and without `max_outsize`
(the bool and the `(bool, Bytes)` results), data from a function argument,
from storage and from `msg.data`, and the keyword operands `value=` and `gas=`
in source order.
`parity-fixtures.txt` selects 7 exact bytecode comparisons, checked in
`evalCompilerRawCallsTheory`; the other sources are related witnesses kept for
diagnostic comparison. Of those, `rc09` and `rc23`, `rc27`, `rc28` match too;
`rc08` and `rc26` differ at runtime byte 54, like the other `concat` witnesses
([issue #566](https://github.com/verifereum/vyper-hol/issues/566)); the
`msg.data` forms (`rc10` to `rc15`, `rc24`) do not finish evaluating within the
probe's 900-second budget.

`oracle/` contains independently generated annotated AST/layout JSON and
deployment/runtime bytecode, with the provenance record of the pinned compiler,
its settings, dependencies and input/output hashes. Reproduce it with the
isolated Python 3.11.11 Vyper installation described in the parent bytecode
README, from the repository root:

```sh
python lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus raw-calls --fixtures /tmp/raw-call-oracle --check
holbuild -j8 build evalCompilerRawCallsTheory
```

For a diagnostic report covering every source:

```sh
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus raw-calls --fixtures /tmp/raw-call-oracle \
  --output /tmp/raw-call-hol
```

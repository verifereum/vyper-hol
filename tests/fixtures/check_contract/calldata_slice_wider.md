`calldata_slice_wider.vy` assigns a 4-byte `slice(msg.data, ...)` to a
`Bytes[100]` local. Vyper types the slice call at `Bytes[100]` and sizes its
buffer by that type. `calldata_slice_wider.json` was generated with Vyper at
`VYPER_PIN` (`577d2534356903076bb79b5b15ebd4d772994693`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/calldata_slice_wider.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/calldata_slice_wider.json --replace "$PWD/="
```

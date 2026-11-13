`slice_folded_length.vy` slices `self.code` with the constant length `N + 1`,
a `Bytes[64]` with the constant length `32 - 4`, and a `Bytes[64]` with a
runtime length. The frontend folds each constant length to a literal, so the
checker bounds the result by it; the runtime length is checked against the
source's bound instead. `slice_folded_length.json` was generated with Vyper
at `VYPER_PIN` (`577d2534356903076bb79b5b15ebd4d772994693`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/slice_folded_length.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/slice_folded_length.json --replace "$PWD/=./"
```

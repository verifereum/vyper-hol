`address_bytes32.vy` converts an address to `bytes32` and `bytes21`, which
Vyper left-pads (`to_bytes_m` computes `shl(256 - 8 * M, addr)`), next to a
`bytes20` to `bytes32` conversion, which it right-pads. `address_bytes32.json`
was generated with Vyper at `VYPER_PIN`
(`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/address_bytes32.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/address_bytes32.json --replace "$PWD/=./"
```

The frontend test checks both runtime and deployment modes.

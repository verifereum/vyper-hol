`address_bytes20.vy` reproduces the address-to-bytes20 checker rejection in
issue #600. `address_bytes20.json` was generated with Vyper at `VYPER_PIN`
(`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/address_bytes20.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/address_bytes20.json --replace "$PWD/=./"
```

The frontend test checks both runtime and deployment modes. Wider
destinations are in `address_bytes32.vy`.

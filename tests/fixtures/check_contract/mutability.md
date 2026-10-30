`mutability.vy` holds functions of every mutability that Vyper accepts: pure
and view functions calling internal pure and view helpers, a `staticcall`,
a static `raw_call`, reads of constants, state, `self.balance` and
`block.number`, a `@nonreentrant` view, `msg.value` in payable functions, and
a nonpayable function that writes state, calls `extcall` and logs.
`mutability.json` was generated with Vyper at `VYPER_PIN`
(`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/mutability.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/mutability.json --replace "$PWD/=./"
```

The forms Vyper rejects can't be compiled to an AST, so their tests build the
AST directly, in `tests/vyperCheckContractLibTestScript.sml`.

`operator_forms.vy` holds the `**`, unary minus and shift forms Vyper accepts
next to the ones the checker rejects: `**` with a literal base, a literal or
folded constant exponent, and `**=` with a literal exponent; unary minus on
signed and decimal values; `<<` by a literal amount (which the annotated AST
types `int8`); `>>` of a signed value by an unsigned amount; and `<<=`/`>>=`
on `uint256`. `operator_forms.json` was generated with Vyper at `VYPER_PIN`
(`9362e36b145c4b63ceb6a893018ea970e78bf6a6`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/operator_forms.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/operator_forms.json --replace "$PWD/=./"
```

The fixture test needs the whole contract accepted, so the forms the checker
rejects are tested on ASTs built directly, in
`tests/vyperCheckContractLibTestScript.sml`. Most of them Vyper rejects too;
`<<=` and `>>=` by a signed amount it accepts.

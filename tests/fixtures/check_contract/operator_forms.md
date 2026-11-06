`operator_forms.vy` holds the `**`, unary minus and shift forms Vyper accepts
next to the ones the checker rejects: `**` with a literal base, a literal or
folded constant exponent, and `**=` with a literal exponent; unary minus on
signed and decimal values; `<<` by a literal amount (which the annotated AST
types `int8`); `>>` of a signed value by an unsigned amount; and `<<=`/`>>=`
on `uint256`. `operator_forms.json` was generated with Vyper at `VYPER_PIN`
(`577d2534356903076bb79b5b15ebd4d772994693`):

```sh
vyper -f annotated_ast,layout tests/fixtures/check_contract/operator_forms.vy > compiler-output.jsonl
python3 tests/sanitize_check_contract_json.py compiler-output.jsonl \
  tests/fixtures/check_contract/operator_forms.json --replace "$PWD/=./"
```

The rejected forms can't be compiled to an AST, so their tests build the AST
directly, in `tests/vyperCheckContractLibTestScript.sml`.

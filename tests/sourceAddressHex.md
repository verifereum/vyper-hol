# Address / bytes20 Source regressions

These regressions distinguish address and bytes20 literals and check the
supported explicit conversion slice, address ↔ bytes20. Wider conversion
destinations are outside this suite's contract.

## Regression purpose

`sourceAddressHexExprTestTheory` checks independent literal categories and exact
dynamic conversion ASTs, including same-type and target-mismatch rejections,
without relying on source-module elaboration.

`sourceAddressHexTestTheory` supplies independent expected modules, exercises
`Source.check_contract`, poisons inferred type/function and folded-value
metadata, and audits kernel theorem tags. The existing
`fixtures/check_contract/address_bytes20.json` also checks agreement with the
ordinary compatible AST in both deployment modes.

Hex tokens remain `SCL_Hex` / `SCV_Hex`, preserving case. BytesM literals require
uniform case and exact length; addresses require exactly 20 bytes and an
independently computed EIP-55 checksum. Inference prefers address when the
checksum is valid, including the case-neutral zero address. Explicit conversion
resolves the destination and independently infers/checks the original argument;
it is not contextual literal coercion. Constant arguments use independently
elaborated declaration types rather than just the token's default category.

Cases cover both dynamic and literal conversion directions, checksummed and
zero addresses, lower/uppercase bytes20, and constants sharing an all-zero token.
Negative cases cover checksums, mixed-case bytes20, lengths and same-type
literal/constant conversions.

## Fixture provenance and reproduction

`sourceAddressHexPin.py` verifies imported compiler implementation bytes against
`VYPER_PIN`, checks independent acceptance expectations, and captures parser
syntax before `vy_ast.get_node` erases source information. Capture uses lexical
annotation, not semantic analysis or folding. Compiler acceptance is not used to
construct the Source AST.

Run from the repository root with the isolated pinned environment:

```sh
.agent-files/folded-value-validation/venv/bin/python -I tests/sourceAddressHexPin.py
holbuild build sourceAddressHexExprTestTheory sourceAddressHexTestTheory \
  --tactic-timeout 2.5
```

Add `--generate` to the pin command only to refresh
`tests/sourceAddressHexFixtures/*.json`.

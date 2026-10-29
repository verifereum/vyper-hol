# Address / bytes20 regressions

These regressions distinguish address and bytes20 literals and check the
supported explicit conversion slice, address ↔ bytes20. Wider conversion
destinations are outside this suite's contract.

## Regression purpose

`sourceAddressHexExprTestTheory` checks independent literal categories and exact
dynamic conversion ASTs, including same-type and target-mismatch rejections,
without relying on source-module elaboration.

`sourceAddressHexTestTheory` retains the independent exact legacy AST check
for `fixtures/check_contract/address_bytes20.json` in both deployment modes.
The ordinary paired `address_bytes20` row checks exact modules, independent
artifacts and delete/poison invariance. Independent full-Source module tests
are extracted with that optional feature.

Hex tokens remain `SCL_Hex` / `SCV_Hex`, preserving case. BytesM literals require
uniform case and exact length; addresses require exactly 20 bytes and an
independently computed EIP-55 checksum. Inference prefers address when the
checksum is valid, including the case-neutral zero address. Explicit conversion
resolves the destination and independently infers/checks the original argument;
it is not contextual literal coercion. Constant arguments use independently
elaborated declaration types rather than just the token's default category.

Expression tests cover literal categories, dynamic conversion directions,
same-type/target mismatch rejection and declaration-derived constant types.
The separate pin-only capture inventory covers checksummed and zero addresses,
lower/uppercase bytes20, constants sharing an all-zero token, bad checksums,
mixed case, lengths and same-type literal/constant conversions.

## Fixture provenance and reproduction

`sourceAddressHexPin.py` verifies imported compiler implementation bytes against
`VYPER_PIN`, checks independent acceptance expectations, and captures parser
syntax before `vy_ast.get_node` erases source information. Capture uses lexical
annotation, not semantic analysis or folding. Compiler acceptance is not used to
construct expected runtime ASTs.

Run from the repository root with the isolated pinned environment:

```sh
.agent-files/folded-value-validation/venv/bin/python -I tests/sourceAddressHexPin.py
holbuild build sourceAddressHexExprTestTheory sourceAddressHexTestTheory \
  --tactic-timeout 2.5
```

Add `--generate` to the pin command only to refresh
`tests/sourceAddressHexFixtures/*.json`.

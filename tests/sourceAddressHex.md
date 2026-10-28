# Address / bytes20 Source regression

`sourceAddressHexPin.py` verifies the imported compiler implementation against
clean `VYPER_PIN`, checks 18 independent acceptance expectations, and captures
actual parser syntax before `vy_ast.get_node` erases source information. Run:

```sh
.agent-files/folded-value-validation/venv/bin/python -I tests/sourceAddressHexPin.py
holbuild build sourceAddressHexExprTestTheory sourceAddressHexTestTheory --tactic-timeout 2.5
```

Use `--generate` only to refresh `sourceAddressHexFixtures/*.json`. Fixture
capture invokes lexical annotation, not semantic analysis or constant folding.
The compiler's acceptance result is not used to construct the Source AST.

`sourceAddressHexExprTestScript.sml` proves the independent literal categories
and exact dynamic conversion ASTs, including same-type and target-mismatch
rejections, without depending on source-module elaboration.

`sourceAddressHexTestScript.sml` states exact expected modules independently,
checks the public `Source.check_contract` API, poisons inferred type/function
and folded-value metadata, and audits kernel theorem tags. For the existing
`fixtures/check_contract/address_bytes20.json`, it also checks exact agreement
with the ordinary compatible AST in both deployment/runtime modes.

Hex tokens remain `SCL_Hex` / `SCV_Hex`, preserving original case. Source
validation distinguishes the two literal domains: uniform-case exact-length
hex for bytesM, versus exactly 20 bytes with independently computed EIP-55 for
address. Inference prefers address when its checksum is valid, including the
case-neutral zero address, just as pinned conversion inference does. Explicit
conversion resolves the destination type operand and independently infers and
checks its original argument; it is not a contextual literal coercion. The
supported conversion slice is exactly address <-> bytes20. Wider destinations
remain outside this slice because their required left padding is not modeled
by the existing shared byte-string conversion.

The ten valid cases cover both dynamic conversion directions, mixed-case
checksummed address, zero address, lower/uppercase bytes20, both literal
conversion directions, and declared address/bytes20 constants sharing the
same all-zero token. The eight invalid cases cover checksum mismatch,
mixed-case bytes20, wrong lengths, and same-type literal/constant conversions.
Constant argument inference uses independently elaborated declaration types,
not just the token's default category.

## Adjacent acceptance inventory (not fixed by this slice)

- `tests/fixtures/check_contract/nested_pop.vy`: both
  `self.items[bucket].pop()` and `self.items[7].pop()` operate on an indexed
  `HashMap[uint256, DynArray[uint256,4]]` receiver. Source expression elaboration
  currently has no append/pop intrinsic/assignment-target path. The ordinary
  regression is `tests/vyperPopReceiverTestScript.sml`.
- `source_module_iterator` already has an array fallback for non-call
  expressions. The pin accepts `for x: uint256 in xs` with `xs: uint256[2]`;
  existing `defaults_control` / `scoped_locals` fixtures cover range rather than
  this ordinary array form, so array-iterator regression coverage is worth
  adding separately. Do not count call-shaped array iteration as an acceptance
  gap: the pin itself rejects `for x: uint256 in self.values()` with
  `IteratorException`, matching Source's range-only call branch.

# F13 — Four source conversion mismatches

**Intended maintainer:** source value conversions and `valid_conversion` typing.
**Disposition: FIXED here**, TASK010–013, landed `a9764fc2`, `8db4d95b`,
`24f682da`, `8e44a5ac` respectively. One report, four original subcases.
[Evidence, history and current audit](README.md).

## Minimal literal counterexamples

| Conversion / input | Old source at `c587772d` | Lowered Venom/EVM and pinned reference; current source |
|---|---|---|
| decimal→int8, **127.0000000001**, represented `DecimalV 1270000000001` | truncates to127, then passes int8 bound | scaled upper bound1270000000000 fails before SDIV; target reverts; current `RuntimeError "convert decimal int"` |
| bytes32→address, **31 zero bytes followed by01** | no clause: `TypeError "convert"`; `valid_conversion` false | unsigned big-endian value1 is `<2**160`; returns address1; current `AddressV 1w` and typing admits it |
| bytes32→decimal, **31 zero bytes followed by01** | no clause: `TypeError "convert"`; `valid_conversion` false | signed scaled representation1, **0.0000000001**, not decimal1.0; current `DecimalV 1` and typing admits it |
| bytes32→bytes4, **12 34 56 78 followed by28 zero bytes** | length32>4 always gives `RuntimeError "convert BytesV bound"` | zero dropped suffix passes; returns bytes4`0x12345678`; current `TAKE 4` succeeds |

For narrowing, changing the **last** dropped byte to01 must still fail. For
bytes→address, first invalid numeric value`2**160` fails the address clamp.
For bytes→decimal, sign is interpreted before Signed168 bounding: all32 bytesFF
represent scaled−1. The address conversion left-pads; decimal conversion
right-pads then arithmetic-shifts. Interchanging those rules is incorrect.
Unsigned decimal conversion also checks before truncation: −0.0000000001→uint8
fails, not0. These literals are definition-level inputs, not assertions that
all are the original fixture's compiled calldata.

## Current definitions, fixtures and regression exports

[Value operations](../../semantics/vyperValueOperationScript.sml),
`evaluate_convert_def`; [typing](../../semantics/type/vyperTypeSystemScript.sml),
`valid_conversion_def`; [type consumers](../../semantics/prop/vyperTypeConversionsScript.sml),
`valid_conversion_no_type_error` / `evaluate_convert_well_typed` remain meaningful.
[Lowering](../../lowering/defs/exprLoweringScript.sml), `compile_type_convert`:
`ConvDecimalToInt`, `ConvBytesToAddress`, `ConvBytesMToDecimal`, `ConvBytesMToBytesM`.

| Fix | Durable exact current regressions | Affected unchanged source fixture |
|---|---|---|
| TASK010 | [decimal](../../tests/vyperDecimalConvertTestScript.sml): `decimal_convert_signed_scaled_boundary`, `decimal_convert_boundaries_eval`, `decimal_convert_boundaries_cv` | [scalar_convert_decimal](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_convert_decimal.vy) |
| TASK011 | [address](../../tests/vyperBytesAddressConvertTestScript.sml): `bytes_address_boundaries_eval`, `bytes_address_all_fixed_lengths_cv`, `bytes_address_fixture_runtime_checked` / `deployment_checked` | [scalar_convert_bytes32_to_address](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_convert_bytes32_to_address.vy) |
| TASK012 | [decimal bytes](../../tests/vyperBytesDecimalConvertTestScript.sml): `bytes_decimal_boundaries_eval`, `bytes_decimal_all_fixed_lengths_cv`, `bytes_decimal_fixture_runtime_checked` / `deployment_checked` | [scalar_convert_bytes32_to_decimal](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_convert_bytes32_to_decimal.vy) |
| TASK013 | [fixed bytes](../../tests/vyperFixedBytesConvertTestScript.sml): `fixed_bytes_narrow_success_iff`, `fixed_bytes_all_length_pairs_cv`, `fixed_bytes_fixture_runtime_checked` / `deployment_checked` | [scalar_convert_bytes32_to_bytes4](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_convert_bytes32_to_bytes4.vy) |

Fixture HOL definitions are in [scalar fixtures](../../lowering/defs/bytecode/eval/evalCompilerSubsetScalarsScript.sml).
F16's first two checker failures are the same TASK011/012 defects, not two
additional unfixed conversions. The unrelated signed int≥135→decimal lower
rounding issue belongs to [F22](F22-outside-supported-lowering.md).

## Reference evidence and static reproduction

Pinned `vyper/builtins/_convert.py`: `_fixed_to_int`124–138 clamps scaled bounds
before SDIV; `_bytes_to_num` uses SAR for signed, SHR for unsigned; `to_address`
430–437 delegates to uint160 conversion; `to_decimal`334–356 decodes signed bytes
and clamps when wider than168; `to_bytes_m`372–389 invokes `bytes_clamp` on fixed-byte
downcasts. `vyper/codegen/core.py:1424–1432`, `bytes_clamp`, asserts zero low bits.
These exact functions were read; no Python conversion/compile was executed here.

Inspect old `evaluate_convert` and `valid_conversion` with `git show c587772d`
and current clauses; substitute each literal, compare the four lowering arms
and reference functions. Read named regression equations for the current
answers. Existing receipts010/011/012/final013 record actual built EVAL/CV,
checker acceptances and scoped saved-object checks (30/34/34/17). Final013
machine receipt parsed here records3820 results,101 historical closed endpoints,
202 unchanged byte lists and original patch preservation; not final060 evidence.

Historical PLAN: §4.2 F13,709–727; D12d–g; §5.3d–g; §5.6 conversion whitelist;
§6.2 conversion row. Historical `evaluate_convert`576–671,
`valid_conversion`387–418 and `compile_type_convert`1576–1680.

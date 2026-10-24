# F16 — Three fixture rejections, including ABI singleton sizing

**Intended maintainer:** source contract/type checker and ABI builtin typing.
**Disposition: FIXED here**, TASK011/012/016; landed `8db4d95b`, `24f682da`,
`707ec670`. [Evidence, history and current audit](README.md).

## Exact counterexamples and behavior

1. `scalar_convert_bytes32_to_address`: bytes32 value31 zeros+01 → address1.
2. `scalar_convert_bytes32_to_decimal`: same bytes → scaled decimal1.
   Both formerly failed `valid_conversion`, so `check_contract` returned
   **NONE**, although lowered/reference conversions succeed. TASK011/012 add
   general valid clauses, not fixture exceptions. See [F13](F13-conversions.md).
3. `abi_dynamic.encode_dynamic("abcdefghijklmnop", 16 bytes01)`: return
   `abi_encode(value, ensure_tuple=False, method_id=0xdeadbeef)` as **Bytes[196]**,
   where `value` has tuple type `(String[16], Bytes[16])`. The TypeBuiltin target
   is **TupleT [TupleT [String[16]; Bytes[16]]]**, and `arg_tys` is the singleton
   list containing that inner tuple type. The evaluator with false ensure
   unwraps the *one argument*, not the two inner tuple fields. Maximum encoded
   inner tuple is192 bytes +4 method ID =196; old checker demanded224+4=228
   from the outer singleton tuple and rejected the unchanged fixture.

For literal maximal inputs above the current evaluator actually encodes196
bytes; with no method ID192. True ensure instead encodes228/224 respectively:
Bytes[196] must reject true ensure. Current predicate preserves this distinction.
These are builtin payload lengths, not external RETURN framing lengths.

## Reproducible checker input and exact layout type

Current saved fixture assertions use
`IS_SOME (check_contract F [] (0w:address) [(NONE, abi_dynamic_program)])`
and the analogous deployment `T`; formerly both returned NONE due to the bound.
Empty layouts are valid here because this pure fixture declares no storage.
The exact argument type is
`(address # (storage_layout # storage_layout)) list`, **not** a single fmap:
[storage_layout](../../semantics/vyperStorageScript.sml) is
`((num option # string) # num) list`. This is the concrete LayoutT shape used
by the checker library's `empty_layouts` quotation. Source namespace key is
`NONE`; checker *failure* NONE is a different option. `[... ]` values for
`evaluate_type_builtin` contain one `ArrayV (TupleV [...])`; source expression
argument evaluation is not an `eval_args NONE` call.

## Current owners, fixtures and reference evidence

- [Checker predicates](../../semantics/type/vyperTypeSystemScript.sml):
  `abi_encode_size_ok tenv ensure target_ty method_id n`,
  `type_builtin_result_ok` passes ensure.
- [Evaluator](../../semantics/vyperContextScript.sml): `evaluate_type_builtin`
  AbiEncode branch / `evaluate_abi_encode_bytes`.
- [Contract checker](../../semantics/type/vyperTypeContractScript.sml): `check_contract`.
- [Permanent tests](../../tests/vyperCheckContractLibTestScript.sml):
  `abi_encode_dynamic_exact_bound`, `abi_encode_dynamic_wrapping_bounds`,
  `abi_encode_wrapping_lengths_eval` / `cv`,
  `abi_dynamic_fixture_runtime_checked` / `deployment_checked`.
- [Actual HOL fixture](../../lowering/defs/bytecode/eval/evalCompilerSubsetAbiBuiltinsScript.sml),
  [unchanged Vyper source](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/abi_dynamic.vy).
- [Lowering encoder](../../lowering/defs/builtinAbiScript.sml),
  [sealed checker computation](../../semantics/type/vyperCheckContractLib.sml):
  ceil32 rewrite repaired computation, not typing assumptions.

Pinned `vyper/builtins/functions.py:2258–2351`, `ABIEncode.fetch_call_return`
and `build_IR`, select `arg_abi_types[0]` / `args[0]` exactly when one argument
and false ensure; add4 for method ID. Export `test_abi_encode.json` actual
`source_code` was inspected (index); it is reference suite provenance, **not**
pretended to be this separately committed ABI-dynamic fixture or a fresh run.

## Reproduction and prior evidence

Read the complete fixture, substitute the maximal literal tuple into
`abi_encode_wrapping_cases_ok`, compare old/current size predicates and pinned
ABIEncode functions. Inspect actual runtime/deployment checker statements above.
TASK016 LOCAL receipt is historically incomplete; **primary016** receipt at
`707ec670` supersedes that checkpoint status:35 focused objects, all six fixture
checks across F13/F16,170 source theories+5 libraries and3820 selected results.
Its JSON was parsed here; no checker, CV, suite or parity was executed by TASK059.

Historical PLAN: §4.2 F16,744–756; D12e/f/j; §5.3j; §6.2 ABI/conversion rows.
Old `abi_encode_size_ok`450–459, source AbiEncode277–290.

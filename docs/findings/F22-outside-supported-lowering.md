# F22 — Lowering differences outside the supported subset

**Intended maintainer:** lowering expression/statement evaluation, storage access,
ABI/events and numeric conversion. **Disposition: BOUNDED by SUPPORTED whitelist;
general fixes DEFERRED.** One report covers the official catalogue; no claim
that introducing a whitelist repairs arbitrary programs.
[Evidence, history and current audit](README.md).

The call/assignment ordering rows below now describe repaired evaluation
orders. Their whitelist admission remains syntactic: the general
Assign/AugAssign simulation cases are still unproved in
[stmtSim](../../lowering/stmtSimScript.sml).

## Minimal concrete definition-level counterexamples

- **Narrow left shift:** uint8 x=128, unsigned shift=1. Source
  `evaluate_binop (Unsigned 8) ... ShL (IntV 128) (IntV 1)` returns `IntV 0`
  (mod256); lowered SHL1,128 leaves **word256**, with no narrow truncation.
  This is an AST/operator-level mismatch; shift variables/literals need not be
  rejected by evaluation. Current whitelist admits ShL only at full-word ints.
- **Non-first storage struct field:** `S={a:uint256,b:uint256}`, module `s:S`
  at slot5, contents5=11,6=22, expression `s.b`. Source reads22. Current
  `compile_attribute` cannot recover struct name from a TopLevelName base,
  so field lookup on empty metadata gives offset0 and reads11. Reads are admitted
  only for first field; writes use a different path and may address every field.
- **Signed int→decimal lower rounding:** input
  **−18707220957835557353007165858768422651596**, e.g. int136 variable.
  This is `floor((-2**167)/10**10)`, one below toward-zero bound
  −18707220957835557353007165858768422651595. Source scales by10**10 then fails
  Signed168 (`RuntimeError`); HOL `ConvIntToDecimal` accepts the floored pre_lo
  and multiplies, yielding scaled−187072209578355573530071658587684226515960,
  outside DecimalT. Legacy reference `_int_to_fixed` clamps toward zero and
  rejects. **Current pinned reference Venom `_to_decimal` also uses floor
  `//`**, agreeing with this lowering at the bad lower edge. Thus the PLAN's
  unqualified "reference rounds toward zero" describes its cited legacy path,
  not every backend in the pinned checkout. Whitelist signed conversions require
  width≤134 (aligned widths therefore≤128), so this136-bit case is excluded.
- **Unsigned negation of zero:** source `Neg` on uint8 `IntV 0` succeeds0.
  Current `compile_neg` emits `SGT 0,0; ASSERT; SUB 0,0`, so aborts before SUB.
  Source negation is **checked**, not wrapped: nonzero unsigned inputs fail the
  source bound. The catalogue's exclusion must not be taken to imply that
  source unsigned negation wraps.
- **Several ABI encode arguments:** `abi_encode(uint256(1),uint256(2))`, true
  ensure, no method ID: source/reference encode tuple(1,2),64 payload bytes;
  HOL TypeBuiltin lowering uses only the first expression/its type, so the
  encoding path supplies one word1, not both1/2. Current supported form requires
  one tuple argument, false ensure and a4-byte method ID; general multi-argument
  ABI behavior is not fixed by F16's checker correction.

These examples reproduce PLAN-listed categories, not newly executed compiled
regressions. No named original fixture exercises these excluded mismatches.

## Entire official catalogue and current boundary

| PLAN F22 category | Current behavior or remaining difference | Current whitelist owner |
|---|---|---|
| Call argument reads | interpreter captures internal argument locations before defaults and reads them afterward; external positional reads follow keyword evaluation, matching the staged lowering phases | `supported_pure_expr` still required for all call operands |
| `x += e` | source and lowering resolve and read the target before evaluating the RHS, then compute and write | `supported_target`, `supported_expr` RHS; root effects admitted |
| `a[i] = e` check order | source and lowering capture the RHS before resolving/checking the target, then read the RHS and store; flat tuple writes resolve/store targets in order | `supported_assignment`, `supported_expr` key/RHS; flat tuple targets admitted, nested tuples excluded |
| Storage struct non-first read | concrete22/11 example above | `supported_storage_field_read` |
| Byte hashmap write keys | source hashes byte keys; lowering read hashes but write uses raw key | `supported_hashmap_key_type`: integer/bool/address only |
| Nested/transient hashmaps | lowering loses type/location on nested/write paths | `supported_declaration_header`, nonnested/nontransient maps |
| Narrow `<<` and integer `~` | source bounds/wraps narrow result; raw SHL/NOT leaves256-bit result | `supported_binop`, `supported_builtin_form` |
| Unsigned negation | source checked negation accepts0; target requires input strictly greater than lower bound0 and rejects0 | signed/decimal Neg only |
| Nonliteral power | source checks mathematical power; target EXP wraps first and bound-checks the wrapped value | power needs a literal base or nonnegative literal exponent |
| Widths not multiple8 | source type/evaluator permits widths; target uses byte-based width/8 clamps | `supported_int_width` |
| Memory-type `empty` | source constructs empty/default aggregate; lowering supplies pointer0 without constructing it | Empty only W |
| Storage Bytes/String | source storage codec versus lowering word/copy representation differs | storage restricted to full-word scalars/arrays/structs |
| Conversions | checker width restrictions apply | width-aware `valid_conversion` relation |
| Several ABI encode args / other flags | concrete example; lower encodes first arg; current dispatcher DOES honor ensure via enc_ty | exact single tuple/false ensure/SOME4-byte ID form |
| ABI decode unwrap flag | source wrapper-sensitive decoding; lowering ignores flag | false flag, identical tuple target/result,≥2 members |
| Indexed aggregate / bytes20 events | incompatible aggregate topics;20-byte values conflated with address encoding | scalar fields; bytes20 excluded |
| Mismatched event args | source checker does not establish declared argument agreement; lowering drops unmatched arguments | `supported_log`: declared exact types/count |
| Bytes/String comparisons | source compares values; lower compares hashes | Eq/NotEq restricted W; no collision-freedom theorem assumed |

## Current files, regression exports and reference evidence

[Source arithmetic/conversion](../../semantics/vyperValueOperationScript.sml),
[interpreter evaluation order](../../semantics/vyperInterpreterScript.sml),
[storage targets](../../semantics/vyperStateScript.sml),
[lowering expressions](../../lowering/defs/exprLoweringScript.sml),
[statements](../../lowering/defs/stmtLoweringScript.sml),
[ABI builtin](../../lowering/defs/builtinAbiScript.sml),
[storage codec](../../semantics/vyperStorageScript.sml),
[event encoding](../../semantics/vyperEventScript.sml).
Current producer boundaries are
[supportedExprForms](../../lowering/supported/supportedExprFormsScript.sml),
[supportedExprs](../../lowering/supported/supportedExprsScript.sml),
[supportedStmts](../../lowering/supported/supportedStmtsScript.sml),
[supportedTypes](../../lowering/supported/supportedTypesScript.sml),
[supportedDecls](../../lowering/supported/supportedDeclsScript.sml).

The whitelist theorems prove **exclusion/support**, not these programs'
semantic correctness: [expression form properties](../../lowering/supported/supportedExprFormPropsScript.sml)
`supported_power_shift_counterexamples`, `conversion_width_boundary_rejection`,
`supported_abi_forms_coverage`; [expression properties](../../lowering/supported/supportedExprPropsScript.sml)
`supported_storage_base_exclusions`, `supported_effect_nesting_counterexamples`;
[statement properties](../../lowering/supported/supportedStmtPropsScript.sml)
`supported_storage_effects_rejected`, `supported_target_exclusions`, `supported_log_statement_row`.

Executable ordering witnesses are in
[evalAssignmentOrder](../../lowering/defs/bytecode/eval/evalAssignmentOrderScript.sml)
(source evaluation and selected exact-bytecode fixtures) and
[vyperLoadTimingTest](../../tests/vyperLoadTimingTestScript.sml)
(storage/memory call arguments and eager builtins). These concrete checks do
not establish the missing general assignment simulation cases.

Pinned reference mappings read: `vyper/builtins/_convert.py:142–154`,
`_int_to_fixed` (toward zero); **`vyper/codegen_venom/builtins/convert.py`,
`_to_decimal`** (floor pre_lo); `vyper/codegen/stmt.py`, `parse_AugAssign`
(cached target, LOAD then arithmetic, restrictions on writes);
`vyper/codegen_venom/expr.py`, `_lower_internal_call` (capture argument
locations before unwrapping; the interpreter now defers these reads too);
`vyper/builtins/functions.py`, `ABIEncode.fetch_call_return`/`build_IR` handles
all args; `vyper/codegen_venom/builtins/abi.py`, `lower_abi_encode`, chooses
single input versus tuple based on ensure. There is no reference run or claim
of frontend acceptance for non-byte-aligned integers/malformed event ASTs.

## Related return-token/FMP and pipeline issues

[Empty INVOKE](F24-empty-invoke-arguments.md) is official F24/TASK024: no user
args gets source token0; nonempty vector gets LAST args. The return-PC token is
opaque in codegen, **not** the concrete assembly address. TASK061's four-field
remap fix and frozen GETFMP witness are linked in [F21](F21-fixed-memory-and-names.md);
neither changes the numeric/ABI/effect-order catalogue above.

F25's driver/DFT schedule is **not owned by TASK059**. Its example
`INVOKE @f; ASSERT %x; MSTORE 0 1; STOP`, x=0, f=`INVALID`, may be reordered
ASSERT first, changing ExHalt_abort to Revert_abort. It motivates forward
pipeline abort transport, not a F22 fix or a request for identical abort kinds.
Current [O1 stages](../../venom/compiler/o1PipelineCorrectScript.sml) S4–S6 remain
admitted; cite [current audit](../compiler-proof-status-2026-10-09.md) rather than
pretending old pass contracts prove the executed driver.

## Reproduction and evidence

Read old/current named clauses, plug in128/1, unsigned zero, slots5/6 and the
exact int136 literal; compare the **two** reference conversion backends.
The old `c587772d` dispatcher already selected `enc_ty` from ensure: the flag
parameter unused inside `lower_abi_encode` is not evidence the whole lowering
ignores ensure. This report corrects that overbroad reading of the catalogue. Inspect rejection
statements and source tuples, not a hypothetical nonexistent test. Receipts019–021
record built boundary properties; final022 records exact101 support membership
proofs. Those receipts do not contain rebuilt whole-run counterexamples for
these sketches. TASK060 and general lowering proof remain open.

Historical PLAN: §4.3 F22,829–847; D11/D19; exact §5.6 rows and §6.2 comparison.
Old int→decimal `exprLoweringScript.sml:1577`, legacy REF142–154;
argument order816–838/1142–1167; struct2107–2135; write order
source1054–1060/847–852 versus lowering978–982/931–955.

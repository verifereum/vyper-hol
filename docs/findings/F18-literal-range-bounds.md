# F18 — Literal ranges cannot carry the zero iteration bound

**Intended maintainer:** statement lowering / frontend AST fixture ownership.
**Disposition: FIXED here**, TASK017, landed `3b176942`.
[Evidence, history and current audit](README.md).

## Minimal counterexample and exact behavior

Original `for_pass` has `For i uint256 (Range (Literal 0) (Literal 2)) 0 body`.
The source enumerates `[0;1]`, checks `compatible_bound (Dynamic 0) 2`, and fails
with `Error (RuntimeError "For too long")`: zero is a capacity bound, not a
source "unbounded literal" sentinel. Old lowering
used the AST bound0 to omit checks, executes two iterations and returns1.
Reference literal `range(2)` has bound2, not0. Current fixture has AST bound2
and source returns1; lowering selects no-check path by **both lowered endpoint
operands being literal**, independent of whether the AST bound equals0.

Five exact repaired AST fields/source results:

| Fixture | Literal endpoints | Old/new bound | Current named source result |
|---|---|---|---|
| for_pass | 0,2 | 0→2 | 1 |
| for_accum | 0,2 | 0→2 | 1 |
| for_continue | 0,3 | 0→3 | 2 |
| for_break | 0,3 | 0→3 | 1 |
| storage_scalar_loop | 0,3 | 0→3 | 7 |

Nonliteral endpoints with bound0 now emit SUB and bounds checks rather than
silently taking the literal fast path. The frontend never emits bound0 for a
nonempty literal range; the malformed hand-written original ASTs are not blamed
on reference source compilation.

## Current owners and reference evidence

- [Lowering](../../lowering/defs/stmtLoweringScript.sml): literal-operand range
  branch; [source](../../semantics/vyperInterpreterScript.sml): For/range bound.
- [Frontend](../../frontend/jsonToVyperExprScript.sml): range-bound construction.
- [Four ASTs](../../lowering/defs/bytecode/eval/evalCompilerScript.sml),
  [storage loop AST](../../lowering/defs/bytecode/eval/evalCompilerSubsetStateScript.sml).
- [Exact regression exports](../../lowering/defs/bytecode/eval/evalCompilerRangeScript.sml):
  `range_literal_operands_skip_checks`, `range_nonliteral_operands_checked`,
  `for_pass_source_result`, `for_accum_source_result`, `for_continue_source_result`,
  `for_break_source_result`, `storage_scalar_loop_source_result`.
- [Original for_pass source](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/for_pass.vy),
  [original storage loop source](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/storage_scalar_loop.vy),
  [four byte endpoints](../../lowering/defs/bytecode/eval/evalCompilerBytecodeControlScript.sml)
  and [storage byte endpoint](../../lowering/defs/bytecode/eval/evalCompilerBytecodeStateScript.sml).

Pinned `vyper/codegen/stmt.py:228–288`, `Stmt._parse_For_range`: without explicit
bound, uses literal `end.int_value()-start.int_value()` for rounds and bound;
with bound, clamps start≤end and uses runtime rounds. Read-only inspection only.

## Reproduction and prior rebuilt evidence

Compare old `git show c587772d` fixture AST bounds and lowering branch with
current linked ASTs; calculate list lengths2/3 and source Dynamic bound check;
inspect all seven regression equations. TASK017 receipt records actual builds
and five unchanged plain-EVAL byte endpoints. At that historical point tag-only
parity checks did not establish Hyp0; later strict certificates are separately
classified in the index, and final060 remains open.

**Official F18 is this range defect**, not ABI ensure (see [F16](F16-fixture-typing-abi-encode.md)).
Historical PLAN: §4.3 F18,778–787; D13 range; §5.6 For row; §6.2 For row.
Old interpreter1070–1076, lowering1244–1311, frontend965–1001.

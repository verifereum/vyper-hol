# F11 — Storage/transient pop must retain the inactive slot

**Intended maintainer:** source storage operations and storage preservation.
**Disposition: FIXED here**, TASK008, landed `dffb4194`.
[Evidence, history and current audit](README.md).

## Minimal counterexample and exact behavior

In `storage_dynarray.append_write_pop(37)`, start with an empty `items` array
(header0), with `anchor` at slot0 and `items` at slot1. Append37, write index0=37,
then pop. Old source returns37 but zeros the popped element; lowered code and
reference return37 and only decrement the length. The header returns to0 while
the old element slot retains37 on target and becomes0 on old source. This is an
observable final-storage mismatch even though the element is outside logical length.

The permanent focused regression uses an even simpler explicit slot map:
array header4=2, element slots5=11 and6=37. Pop returns `IntV 37`, header4=1,
slot6=37, slot5=11; **only the header changes**. Old source instead wrote slot6=0.
Both storage and transient backends now use the one-header-write behavior;
empty pop still errors without changing state. `slots_in_range` examines only
indices below the new length, not a promise that discarded storage is zero.

## Current owners and reference evidence

- [Source](../../semantics/vyperStateScript.sml): `assign_target`, storage/transient
  `PopOp` tail (read old value, nonempty check, decrement, one write).
- [Exact witnesses](../../tests/vyperStoragePopTestScript.sml):
  `storage_pop_nonzero_slot_retained`, `transient_pop_nonzero_slot_retained`,
  `storage_pop_cv_slots`, `transient_pop_cv_slots`, empty-pop equations.
- [Storage reconstruction](../../semantics/prop/vyperStorageWritePreservationScript.sml)
  and [type preservation](../../semantics/prop/vyperTypeStoragePreservationScript.sml).
- [Lowering](../../lowering/defs/exprLoweringScript.sml): `compile_dynarray_pop`.
- [Original Vyper fixture](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/storage_dynarray.vy),
  [HOL fixture](../../lowering/defs/bytecode/eval/evalCompilerSubsetStateScript.sml).

Pinned reference `vyper/codegen/core.py:520–542`, `pop_dyn_array`:
`STORE(darray_node,new_len)` only; optional popped-item pointer uses the old
slot without clearing it. Reference dynamic-array export hash was inspected
as recorded in the index, not rerun or narrowed.

## Reproduction and evidence distinction

Read the exact `pop_test_context`/`pop_test_state` and theorem equations;
compare `git show c587772d:semantics/vyperStateScript.sml` PopOp's default
write and current tail with the slot map above. Inspect the unchanged fixture's
`append_write_pop` source and reference `pop_dyn_array` for the fixture-level
mismatch. These are static derivations, not a newly executed storage transaction.
TASK008 receipt records eight actually built regressions/EVAL/CV witnesses and
historical3820 selected results. No final-source suite or byte list was replayed here.

Historical PLAN: §4.2 F11, lines694–702; D12b; §5.3b; §6.2 dynamic-array row.
Original source `vyperStateScript.sml:933–945` (default write941),
`exprLoweringScript.sml:995–1013`; invariant
`vyperLookupStorageScript.sml:81–118`.

# Frozen type-builtin obligation: checked counterexample

The frozen `type_builtin_expr_ptr_ok` is false. Its statement has not been changed.

## Checked result

`bodyPtrTypeBuiltinsPaddingCounterexampleTheory` exports
`type_builtin_expr_ptr_ok_counterexample`: a concrete instance of the frozen
antecedent together with the negation of its conclusion. Build with
`holbuild(targets=["bodyPtrTypeBuiltinsPaddingCounterexampleTheory"])`.
The target's original admission is deliberately not replaced by a purported proof.

## Instance and frame

- Context: `padding_actual_context`, the singleton internal pure `probe` program
  in `bodyPtrTypeBuiltinsPaddingWitnessScript.sml`.
- Expression: `convert(x, int256)`, where `x : Bytes[1]` is the Name operand
  `Name (BaseT (BytesT (Dynamic 1))) "x"` and has source value `BytesV [0w]`.
- The universal singleton operand judgment is independently proved by
  `padding_operand_universal`, without importing the frozen target or pointer main.
- Memory bytes 0..31 encode length 1; byte32 is 0; the remaining bytes through63
  are also physically 0. The allocation covers [0,64), and its pointer is `%5=0`.
  `%6=0` is the saved return PC; `%7=64` is the separately allocated return slot.
- Entry machine is `padding_actual_machine` at the actual compiled block, index3.
  Initial provenance is `FEMPTY |+ ("%5",(0,64))`; initial taint is
  `entry_taint with t_mem := {63}`. Thus only an unused padding byte is tainted.
- `padding_actual_body_inv`, `padding_actual_body_pre`,
  `padding_actual_stmt_state_rel`, `padding_actual_entry_static`, and
  `padding_actual_ghost_entry` establish the complete entry frame unconditionally.
  Robust bytes representation tolerates arbitrary changes to byte63, because the
  logical value occupies only byte32. Allocation coverage does not imply padding
  cleanliness.

## Obstruction and exclusion of alternative outcomes

The actual compiled prefix is:

```
idx3: %8  = MLOAD %5             // length = 1
idx4: %9  = ADD %5 32            // data address = 32
idx5: %10 = MLOAD %9             // value = 0, taint = {31}
idx6: %11 = ISZERO %8
idx7: %12 = ISZERO %11           // value = 1
idx8: %13 = MUL %10 %12          // forbidden: tainted scalar operand %10
```

The remaining SUB/MUL/SAR would finish the expression at index12. The pointer
checker rejects the MUL at index8 even though the eventual shifted semantic
value is zero and padding taint would be discarded by the positive-length SAR.
Physical zero bytes do not remove ghost taint.

`PaddingOutcomeTheory` checks each concrete machine transition and taint
projection, and then proves structurally that **every** pointer path from this
entry stops in OK at one of indices3..8. Reflexive and shorter paths are allowed;
none meets the required final index12, and none exits. Source evaluation is
checked to return `IntV 0` for arbitrary gas observations, ruling out the separate
`gas_exempt_cert` alternative. `padding_actual_no_pointer_outcome` therefore
excludes the entire counted-pointer outcome, not merely one chosen trace.
The final leaf uses this result to prove `padding_actual_expr_sim_ptr_false`,
`padding_body_expr_ptr_ok_false`, and the concrete frozen-target counterexample.

## Tight local sufficient repair (not implemented)

With the current instruction order and pointer checker, the exact missing local
condition is that the **whole data word read by the scalar conversion** is clean:

```
mem_word_taint tn.t_mem (data_address) = {}
```

Equivalently, no byte in `[data_address,data_address+32)` may be tainted at that
MLOAD. For this concrete frame this means excluding byte63 from memory taint.
Logical occupied-byte cleanliness and 64-byte pointer coverage are insufficient.
Requiring the whole allocation clean is stronger than necessary: only the actual
32-byte data read (in addition to the already clean header) needs this repair.
A strengthened bytes representation/frame invariant can supply that condition;
that changes an unowned invariant, so it has not been implemented here. Another
possible repair is a different lowering that discards/avoids padding before any
instruction requiring clean scalar operands, with a separately checked empty
case. Merely moving the existing MUL after an unqualified SAR is not certified
as a repair for empty bytestrings.

These are sufficient repairs to the demonstrated local taint obstruction, not a
claim that all other branches of a globally repaired type-builtin theorem have
been proved. The frozen statement itself cannot be proved under the present
invariants and lowering.

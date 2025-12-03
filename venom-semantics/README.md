# Venom Semantics

Formal semantics for the Venom IR (Vyper's intermediate representation) in HOL4.

## Building

Requires HOL4 and verifereum. Set `VFMDIR` to point to your verifereum checkout:

```bash
export VFMDIR=/path/to/verifereum
cd theories
Holmake
```

## Structure

- `theories/` - HOL4 theory files
  - `venomStateScript.sml` - Execution state definition
  - `venomInstScript.sml` - Instructions and basic blocks
  - `venomSemScript.sml` - Operational semantics and effects

## Overview

Venom is a register-based SSA IR that targets the EVM. Uses types from verifereum (`bytes32`, `storage`, etc.).

### Data Types
- `Lit bytes32` - Literal 256-bit values
- `Var string` - SSA variables (e.g., `%1`)
- `Label string` - Basic block labels (e.g., `@block1`)

### Instructions
Instructions have the form: `%output = opcode operand1, operand2, ...`

Categories:
1. **Arithmetic**: add, sub, mul, div, mod, exp, addmod, mulmod
2. **Comparison**: eq, lt, gt, slt, sgt, iszero
3. **Bitwise**: and, or, xor, not, shl, shr, sar
4. **Memory**: mload, mstore, mcopy
5. **Storage**: sload, sstore
6. **Transient**: tload, tstore
7. **Control flow**: jmp, jnz, djmp, ret, return, revert, stop, sink
8. **Calls**: call, staticcall, delegatecall, invoke
9. **SSA**: phi, param, assign

### Basic Blocks
- Must end with a terminator (jmp, jnz, djmp, ret, return, revert, stop, sink)
- Phi nodes must come first (resolved using `vs_prev_bb` in state)
- Connected via CFG edges

### Effects System
Instructions can read/write effects (used for optimization):
- STORAGE, TRANSIENT, MEMORY, MSIZE
- IMMUTABLES, RETURNDATA, LOG
- BALANCE, EXTCODE

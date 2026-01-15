# Venom Semantics

Formal semantics for the Venom IR (Vyper's intermediate representation) in HOL4.

## Building

```bash
export VFMDIR=/path/to/verifereum
cd venom
Holmake
```

## Files

- `venomStateScript.sml` - Execution state, operands, state operations
- `venomInstScript.sml` - Instructions, basic blocks, functions
- `venomSemScript.sml` - Operational semantics

## Structure

- `analysis/` - analysis definitions (see `venom/analysis/README.md`)
- `passes/` - pass definitions (see `venom/passes/README.md`)
- `compiler/` - shared compiler infrastructure (see `venom/compiler/README.md`)
- `optimization_levels/` - optimization pipeline definitions (see `venom/optimization_levels/README.md`)

All compiler passes and analyses in this tree are definition-only ports of the
Python compiler; proofs live elsewhere.

## Execution State (`venom_state`)

| Field | Type | Description |
|-------|------|-------------|
| `vs_vars` | `string |-> bytes32` | SSA variable bindings |
| `vs_memory` | `byte list` | Byte-addressable memory |
| `vs_storage` | `storage` | Persistent storage |
| `vs_transient` | `storage` | Transient storage (EIP-1153) |
| `vs_prev_bb` | `string option` | Previous block (for PHI resolution) |
| `vs_current_bb` | `string` | Current basic block label |
| `vs_inst_idx` | `num` | Instruction index within block |

## Semantics

- `step_inst` - Execute single instruction, returns `exec_result`
- `run_block` - Run block until terminator
- `run_function` - Run function across blocks (fuel-bounded)

`exec_result` = `OK state` | `Halt state` | `Revert state` | `Error string`

Instructions update state via `update_var` (for outputs) and operations like `mstore`, `sstore`. Control flow uses `jump_to` which sets `vs_prev_bb` and resets `vs_inst_idx`.

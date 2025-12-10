# SSA Construction Proof Plan

## Current State (2025-12-10)

**Theories build with 4 cheats in ssaBlockTheory**:
1. `jnz_result_ssa_equiv` - **Interactive proof verified, batch mode fails** (TRY/NO_TAC interaction)
2. `step_inst_result_ssa_equiv` - **Interactive proof verified, batch mode fails** (simp[] expands tuple cases)
3. `step_in_block_ssa_result_equiv` - Transitively cheated (depends on step_inst)
4. `run_block_ssa_equiv` - Induction challenge with two different blocks

**Fully Proven (no cheats)**:
- `exec_binop_result_ssa_equiv` - Added LENGTH <= 1 precondition, now fully proven
- `exec_unop_result_ssa_equiv` - Added LENGTH <= 1 precondition, now fully proven
- `exec_modop_result_ssa_equiv` - Added LENGTH <= 1 precondition, now fully proven
- `jmp_result_ssa_equiv` - Fully proven via case splits + jump_to_ssa_equiv
- `mload_result_ssa_equiv`, `sload_result_ssa_equiv`, `tload_result_ssa_equiv` - Fully proven
- `mstore_result_ssa_equiv`, `sstore_result_ssa_equiv`, `tstore_result_ssa_equiv` - Fully proven
- `assign_result_ssa_equiv` - Fully proven
- Helper theorems in ssaStateEquivTheory - Fully proven

### step_inst_result_ssa_equiv Issue (Dec 2025)

**Interactive proof works** (verified in HOL session):
- After `Cases_on \`inst.inst_opcode\` >> simp[]` (NOT gvs[]), goals have correct form
- Binop/unop/modop: `irule exec_*_result_ssa_equiv >> gvs[inst_ssa_compatible_def] >> output case splits >> FLOOKUP case split`
- Example ADD case interactively proven: irule + Cases_on outputs + Cases_on t + Cases_on FLOOKUP

**Batch mode issue**:
- `simp[]` in tactic sequence expands tuple case expressions to nested cases
- Helper theorems use tuple patterns `case (a, b) of ([x], [y]) => ...`
- Goal has nested patterns `case a of [x] => case b of [y] => ...`
- `irule` can't match due to syntactic difference

**Potential fixes**:
1. Rewrite helper theorems to use expanded patterns (tedious but straightforward)
2. Use `ONCE_REWRITE_TAC` with theorem in both directions
3. Keep cheat and document as technical HOL4 issue

### jnz_result_ssa_equiv Issue (Dec 2025)

**Interactive proof works** - case splits on operand structure, eval_operand_ssa_equiv for condition,
IF_CASES_TAC for branch, jump_to_ssa_equiv for both branches.

**Batch mode fails** - `TRY/NO_TAC` interaction with `rename1` in case splits doesn't work
in batch mode. Error: "FIRST_ASSUM: raised".

### Progress Summary

**Completed Proofs (without cheats)**:
- `valid_ssa_transform_compatible` - Proven via wf_blocks_ssa_compatible_eq
- `exec_binop_ssa_equiv`, `exec_unop_ssa_equiv`, `exec_modop_ssa_equiv` - Proven
- `exec_binop_result_ssa_equiv`, `exec_unop_result_ssa_equiv`, `exec_modop_result_ssa_equiv` - Proven
- `step_inst_halt_ssa_equiv`, `step_inst_revert_ssa_equiv` - Proven
- `step_inst_non_phi_ssa_equiv` - Proven (OK case dispatches to result_ssa_equiv)
- `next_inst_ssa_equiv` - Proven (preserves ssa_state_equiv)
- `jmp_result_ssa_equiv` - Proven
- `mload_result_ssa_equiv`, `sload_result_ssa_equiv`, `tload_result_ssa_equiv` - Proven
- `mstore_result_ssa_equiv`, `sstore_result_ssa_equiv`, `tstore_result_ssa_equiv` - Proven
- `assign_result_ssa_equiv` - Proven
- Helper theorems in ssaStateEquivTheory - Proven

**Proof Structure Complete (transitively cheated)**:
- `step_in_block_ssa_result_equiv` - Logic correct, depends on step_inst_result_ssa_equiv
- `run_block_ssa_equiv` - Induction structure outlined, needs IH fix

### Key Definition Fix Applied
Fixed `inst_ssa_compatible_def` freshness condition from:
```sml
(!v. FLOOKUP vm v = NONE ==> v <> ssa_out)  (* Wrong *)
```
to:
```sml
(!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)  (* Correct *)
```

## Remaining Work

### 1. Fix step_inst_result_ssa_equiv batch mode

Two approaches being considered:
1. **Rewrite helper theorems** to use expanded case patterns (partially done for stores)
2. **Avoid simp[] expansion** by using `CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV thm))` or similar

### 2. Fix jnz_result_ssa_equiv batch mode

Try different tactic sequencing:
- Avoid `rename1` in favor of positional tactics
- Consider using `fs[]` instead of `simp[]`

### 3. run_block_ssa_equiv (induction challenge)

The proof requires inducting on `run_block fn bb s_orig` while carrying `bb_ssa` and `s_ssa`.
Use `fs[]` instead of `gvs[]` to preserve assumptions across recursive calls.

### 4. run_function_ssa_equiv

Depends on run_block_ssa_equiv. Standard induction on fuel.

## File Organization

```
ssaBlockScript.sml (~1000 LOC)
├── Instruction-level helpers (eval_renamed_operand, exec_*_ssa_equiv)
├── inst_ssa_compatible_def
├── Helper theorems (jmp_result_ssa_equiv, mload_result_ssa_equiv, etc.)
├── Store/assign result equiv theorems (mstore, sstore, tstore, assign)
├── step_inst_*_ssa_equiv theorems
├── step_in_block_ssa_result_equiv
└── run_block_ssa_equiv

ssaFunctionScript.sml (~100 LOC)
└── run_function_ssa_equiv (depends on run_block_ssa_equiv)
```

## Testing Strategy

Once cheats are removed:
1. Build with `VFMDIR=/home/ubuntu/verifereum Holmake`
2. Verify no CHEAT messages in build output
3. Check theory export succeeds

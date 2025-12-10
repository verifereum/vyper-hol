# SSA Construction Proof Plan

## Current State (2025-12-10)

**Theories build with 4 cheats in ssaBlockTheory**:
1. `jnz_result_ssa_equiv` - **Interactive proof verified, batch mode fails** (TRY/NO_TAC interaction)
2. `step_inst_result_ssa_equiv` - **Pattern matching issue**: helper theorems proven, but irule fails due to `gvs[AllCaseEqs()]` expanding case structures
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

### step_inst_result_ssa_equiv Issue (Dec 2025)

**Problem**: The helper theorems (jmp_result_ssa_equiv, mstore_result_ssa_equiv, etc.) are proven,
but `irule` fails to match them in the main proof. Root cause:

1. Main proof uses `gvs[AllCaseEqs()]` which expands case expressions:
   ```sml
   (* Before: *)
   case (eval_operand op1 s, eval_operand op2 s) of (SOME v1, SOME v2) => ...
   (* After: *)
   case eval_operand op1 s of NONE => ... | SOME v1 =>
     case eval_operand op2 s of NONE => ... | SOME v2 => ...
   ```

2. Helper theorems use the original (unexpanded) pattern, so irule can't match.

**Potential fixes**:
- Update helper theorems to use expanded case structures (done for mstore/sstore/tstore)
- Avoid `AllCaseEqs()` expansion in the main proof
- Use `simp[theorem]` instead of `irule theorem`

### jnz_result_ssa_equiv Issue (Dec 2025)

**Interactive proof works** (verified in .hol_cmd.sml session):
```sml
(* Key steps: *)
rw[] >> simp[AllCaseEqs(), ssa_result_equiv_def, ssa_operand_def] >>
Cases_on `inst.inst_operands` >> simp[ssa_result_equiv_def] >>
(* ... case splits on op1::rest1, op2, op3, rest3 ... *)
(* For Var cases: CASE_TAC >> simp[ssa_result_equiv_def] *)
(* For valid [op1; Label lbl2; Label lbl3] case: *)
`eval_operand op1 s_orig = eval_operand (ssa_operand vm op1) s_ssa` by
  (irule eval_operand_ssa_equiv >> simp[]) >>
simp[] >> Cases_on `eval_operand (ssa_operand vm op1) s_ssa` >> simp[ssa_result_equiv_def] >>
IF_CASES_TAC >> simp[ssa_result_equiv_def] >>
irule jump_to_ssa_equiv >> simp[]
```

**Batch mode fails** with `FIRST_ASSUM: raised`. Root cause appears to be:
- `TRY (CASE_TAC >> simp[ssa_result_equiv_def] >> NO_TAC)` doesn't behave correctly
- `rename1` may interact poorly with subgoals created by case splits

**Workaround**: Using cheat with documented interactive proof. Can revisit later.

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

### 1. Fix step_inst_result_ssa_equiv pattern matching

Two approaches:
1. **Avoid AllCaseEqs expansion**: Use `simp[]` instead of `gvs[AllCaseEqs()]` to preserve case structure
2. **Update helper theorems**: Match expanded patterns exactly (partially done for stores)

### 2. Fix jnz_result_ssa_equiv batch mode

The interactive proof works. Need to investigate:
- Try different tactic sequencing (separate `e()` calls)
- Try avoiding `rename1` in favor of positional tactics
- Consider using `fs[]` instead of `simp[]`/`gvs[]`

### 3. run_block_ssa_equiv (induction challenge)

The proof requires inducting on `run_block fn bb s_orig` while carrying `bb_ssa` and `s_ssa`. The challenge is that `completeInduct_on` creates an IH with `bb_ssa` fixed from outer scope, but `gvs[]` may consume/modify assumptions.

**Proposed fix**: Use `fs[]` instead of `gvs[]` to preserve assumptions, or manually manage the IH with `qpat_x_assum`.

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

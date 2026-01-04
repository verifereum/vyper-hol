# PROOF_DESIGN: make_ssa

This document presents the mathematical proof plan for the SSA construction correctness proof. It describes the main goals and the argument structure that a proof script must formalize.

The key ingredients are:
- **SSA state equivalence** (`ssa_state_equiv`) and **result equivalence** (`ssa_result_equiv`), defined in `ssaStateEquiv`.
- **Instruction compatibility** (`inst_ssa_compatible`) and **valid transform** (`valid_ssa_transform`), defined in `ssaBlockCompat` and `ssaWellFormed`.
- **Operational semantics** (`step_inst`, `step_in_block`, `run_block`, `run_function`) from `venomSem`.

Below, each theorem is presented in the planner format. All claims are explicitly tied to definitions or already-proved lemmas.

---

## Theorem: step_inst_result_ssa_equiv

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)
For any instruction `inst`, its SSA-transformed counterpart `inst_ssa`, and SSA-equivalent states `s_orig`, `s_ssa` under mapping `vm`, if:
- `inst_ssa_compatible vm inst inst_ssa`,
- `inst.inst_opcode <> PHI`,
- `LENGTH inst.inst_outputs <= 1`,
then
`ssa_result_equiv vm (step_inst inst s_orig) (step_inst inst_ssa s_ssa)`.

## Key Insights
1. The semantics `step_inst` is a case split over opcodes; each opcode is handled by a dedicated result-equivalence lemma in the `ssaBlockResult*` theories or by a shared helper.
2. Operand evaluation is preserved by `eval_operand_ssa_equiv` (from `ssaStateEquiv`), which follows from `ssa_state_equiv` and `ssa_operand_def`.
3. Output freshness and operand mapping are guaranteed by `inst_ssa_compatible_def`, enabling `update_var_ssa_equiv` and related state-equivalence lemmas.

## Validated Assumptions (ALL must be VERIFIED)
- `inst_ssa_compatible vm inst inst_ssa`: **VERIFIED** by `inst_ssa_compatible_def` (opcode equality, operand mapping, output freshness).
- `ssa_state_equiv vm s_orig s_ssa`: **VERIFIED** by `ssa_state_equiv_def` (var map equivalence plus equality of all non-variable state components).
- `step_inst` structure: **VERIFIED** by `step_inst_def` in `venomSem` (explicit opcode cases).
- Non-PHI and single-output preconditions: **VERIFIED** as explicit hypotheses of the goal.

## Preliminary Facts to Establish
1. `eval_operand_ssa_equiv`: operand evaluation respects SSA mapping; needed for all instruction classes that read operands.
2. `update_var_ssa_equiv`, `write_memory_with_expansion_ssa_equiv`, `jump_to_ssa_equiv`, `halt_state_ssa_equiv`, `revert_state_ssa_equiv`: preserve `ssa_state_equiv` for state updates.
3. Specialized result-equivalence lemmas for opcode families:
   - Arithmetic/bitwise: `exec_binop_result_ssa_equiv`, `exec_unop_result_ssa_equiv`, `exec_modop_result_ssa_equiv`.
   - Memory/storage: `mload_result_ssa_equiv`, `sload_result_ssa_equiv`, `tload_result_ssa_equiv`, `mstore_result_ssa_equiv`, `sstore_result_ssa_equiv`, `tstore_result_ssa_equiv`.
   - Context/hash: `assert_result_ssa_equiv`, `assert_unreachable_result_ssa_equiv`, `blockhash_result_ssa_equiv`, `balance_result_ssa_equiv`, `calldataload_result_ssa_equiv`, `sha3_result_ssa_equiv`, `sha3_64_result_ssa_equiv`.
   - Copy/control: `calldatacopy_result_ssa_equiv`, `returndatacopy_result_ssa_equiv`, `assign_result_ssa_equiv`, `jmp_result_ssa_equiv`, `jnz_result_ssa_equiv`.

## Proof Argument
### Case Split on `inst.inst_opcode`
By `step_inst_def`, each opcode yields one of:
- an `exec_binop/exec_unop/exec_modop` result,
- a memory or storage read/write,
- a control-flow change,
- a context/hashing operation,
- a copy/assign operation,
- a termination (`Halt`/`Revert`) or error.

For each opcode class:
1. **Arithmetic/bitwise/mod**: apply `exec_*_result_ssa_equiv`; its premises are satisfied by operand mapping from `inst_ssa_compatible_def` and `eval_operand_ssa_equiv`, and output freshness (single-output hypothesis plus `inst_ssa_compatible_def`).
2. **Loads/stores**: apply the corresponding `*_result_ssa_equiv` lemma. These lemmas rely only on operand evaluation equivalence and equality of memory/storage components in `ssa_state_equiv_def`.
3. **Context/hash**: apply the `ssaBlockResultContext` lemmas; equality of contexts is guaranteed by `ssa_state_equiv_def`.
4. **Copy/assign/jump**: apply the `ssaBlockResultCopy` lemmas; their premises use operand mapping and, where needed, output compatibility from `inst_ssa_compatible_def`.
5. **Halt/Revert/Error**: these are handled by the above lemmas for assert/returndatacopy and by `ssa_result_equiv_def` for error cases.

Each case discharges to a direct application of the relevant lemma; no additional invariants are required beyond the stated hypotheses.

## Required Lemmas
- `eval_operand_ssa_equiv` (available in `ssaStateEquiv`).
- `update_var_ssa_equiv`, `write_memory_with_expansion_ssa_equiv`, `jump_to_ssa_equiv`, `halt_state_ssa_equiv`, `revert_state_ssa_equiv` (available in `ssaStateEquiv`).
- The opcode-specific `*_result_ssa_equiv` lemmas listed above (available in `ssaBlockResultCore`, `ssaBlockResultMem`, `ssaBlockResultContext`, `ssaBlockResultCopy`).

## Potential Difficulties
- Ensuring the correct opcode class is used; this is resolved by `step_inst_def` which explicitly enumerates opcode behavior.
- Output freshness conditions for single-output instructions; these are guaranteed by `inst_ssa_compatible_def` and the single-output hypothesis.

---

## Theorem: step_in_block_ssa_result_equiv

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)
Given two blocks `bb` and `bb_ssa` of equal length, an SSA mapping `vm`, and SSA-equivalent states `s_orig`, `s_ssa`, if every instruction pair is `inst_ssa_compatible`, non-PHI, and single-output, then the pair of results returned by `step_in_block` are SSA-equivalent and have the same terminator flag.

## Key Insights
1. `ssa_state_equiv_def` gives equality of `vs_inst_idx`, so `get_instruction` indexes the same position in both blocks.
2. `step_inst_result_ssa_equiv` gives equivalence for the instruction at that index under the non-PHI/single-output assumptions.
3. `is_terminator` is preserved because opcodes are identical under `inst_ssa_compatible_def`.
4. If the instruction yields `OK`, `next_inst` preserves `ssa_state_equiv` by `next_inst_ssa_equiv`.

## Validated Assumptions (ALL must be VERIFIED)
- Index equality: **VERIFIED** by `ssa_state_equiv_def` (equality of `vs_inst_idx`).
- Instruction compatibility/shape: **VERIFIED** by the explicit hypotheses in the theorem statement.
- `step_in_block` structure: **VERIFIED** by `step_in_block_def` in `venomSem`.

## Preliminary Facts to Establish
1. `next_inst_ssa_equiv`: updates the instruction index while preserving `ssa_state_equiv`.
2. `step_inst_result_ssa_equiv`: instruction-level result equivalence (previous theorem).

## Proof Argument
### Case 1: `get_instruction` returns NONE
By `step_in_block_def`, both sides return `Error "block not terminated"` and the terminator flag is `T`, yielding `ssa_result_equiv` by definition.

### Case 2: `get_instruction` returns SOME `inst`
- Use `inst_ssa_compatible` for the indexed instruction pair, together with non-PHI and single-output assumptions.
- Apply `step_inst_result_ssa_equiv` to obtain `ssa_result_equiv` for the instruction step results.
- If the result is `OK`, compare the `is_terminator` flag using opcode equality and apply `next_inst_ssa_equiv` in the non-terminator branch.
- If the result is `Halt`, `Revert`, or `Error`, `ssa_result_equiv_def` already forces matching result constructors.

## Required Lemmas
- `step_inst_result_ssa_equiv`.
- `next_inst_ssa_equiv`.
- `ssa_result_equiv_def`.

## Potential Difficulties
- Ensuring the block indices align; guaranteed by `ssa_state_equiv_def`.

---

## Theorem: run_block_ssa_equiv

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)
For blocks `bb` and `bb_ssa` of equal length with pointwise `inst_ssa_compatible` instructions (non-PHI, single-output), and SSA-equivalent initial states, `run_block` produces SSA-equivalent results.

## Key Insights
1. `run_block_def` is defined by repeated calls to `step_in_block`; use the standard induction principle `run_block_ind`.
2. The step-level equivalence from `step_in_block_ssa_result_equiv` aligns the next state/result and the terminator flag.
3. The measure used in `run_block_ind` decreases when `step_in_block` returns `OK` with a non-terminator, so the induction is valid.

## Validated Assumptions (ALL must be VERIFIED)
- `run_block_def` and its induction principle: **VERIFIED** by `venomSem` definitions and the provided `run_block_ind`.
- The step-level hypothesis on every instruction: **VERIFIED** by explicit hypotheses.

## Preliminary Facts to Establish
1. `step_in_block_ssa_result_equiv` (previous theorem).
2. Equality of `vs_halted` and other control fields under `ssa_state_equiv_def`.

## Proof Argument
### Inductive Structure
Induct on `run_block` using `run_block_ind`.

### Inductive Step
Unfold `run_block_def` and split on `step_in_block`:
- If `step_in_block` returns `Halt`, `Revert`, or `Error`, apply `step_in_block_ssa_result_equiv` to align the result constructors, then conclude via `ssa_result_equiv_def`.
- If it returns `OK s'`, use `step_in_block_ssa_result_equiv` to obtain the SSA-equivalent `s'_ssa` and the same terminator flag. If the flag is `T`, the block ends and `ssa_result_equiv_def` closes the goal. If the flag is `F`, apply the induction hypothesis to the recursive call because the measure decreases when `next_inst` advances the instruction index.

## Required Lemmas
- `step_in_block_ssa_result_equiv`.
- `ssa_result_equiv_def`.

## Potential Difficulties
- Correctly propagating the terminator flag; it is equal by `step_in_block_ssa_result_equiv`.

---

## Theorem: run_function_ssa_equiv

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)
For fuel `fuel`, functions `fn` and `fn_ssa`, and SSA-equivalent states `s_orig`, `s_ssa`, if `fn_ssa_compatible vm fn fn_ssa` and `wf_input_fn fn`, then
`ssa_result_equiv vm (run_function fuel fn s_orig) (run_function fuel fn_ssa s_ssa)`.

## Key Insights
1. `run_function_def` performs a lookup of the current block and calls `run_block`. The SSA-compatible function yields a corresponding SSA block via `lookup_block_ssa_compatible`.
2. `wf_input_fn` implies `no_phi_fn` and `single_output_fn`, which provide the non-PHI and single-output prerequisites for block-level equivalence.
3. `run_block_ssa_equiv` establishes result equivalence for each block execution; the `OK` case recurses on the next block and uses the induction hypothesis on fuel.

## Validated Assumptions (ALL must be VERIFIED)
- `fn_ssa_compatible_def`: **VERIFIED** in `ssaFunction` (same name, same number of blocks, blockwise `inst_ssa_compatible`).
- `wf_input_fn_def`: **VERIFIED** in `ssaWellFormed` (includes `no_phi_fn` and `single_output_fn`).
- `run_function_def`: **VERIFIED** in `venomSem`.

## Preliminary Facts to Establish
1. `lookup_block_ssa_compatible` and `lookup_block_ssa_compatible_none` for corresponding block selection.
2. Derivations from `wf_input_fn`:
   - `no_phi_fn` ⇒ every instruction opcode is not `PHI`.
   - `single_output_fn` ⇒ every instruction has at most one output.
3. `run_block_ssa_equiv` (previous theorem).

## Proof Argument
### Induction on fuel
- **Base case (`fuel = 0`)**: both sides return `Error "out of fuel"` by `run_function_def`, and `ssa_result_equiv_def` holds.
- **Inductive step**:
  1. Use `ssa_state_equiv_def` to show `s_orig.vs_current_bb = s_ssa.vs_current_bb`.
  2. Apply `lookup_block_ssa_compatible` to obtain corresponding blocks `bb` and `bb_ssa` (or both fail). Failure cases yield `Error` on both sides and are equivalent by `ssa_result_equiv_def`.
  3. From `wf_input_fn`, derive non-PHI and single-output conditions for every instruction in `bb`.
  4. Apply `run_block_ssa_equiv` to the block execution.
  5. If `run_block` returns `OK` and not halted, use the induction hypothesis on `fuel-1` with the updated states; otherwise conclude by `ssa_result_equiv_def`.

## Required Lemmas
- `lookup_block_ssa_compatible` / `lookup_block_ssa_compatible_none`.
- `run_block_ssa_equiv`.
- Consequences of `wf_input_fn` (`no_phi_fn`, `single_output_fn`).

## Potential Difficulties
- Ensuring the block-level prerequisites (non-PHI and single-output) hold; this is guaranteed by `wf_input_fn_def`.

---

## Theorem: ssa_construction_correct

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)
If `valid_ssa_transform fn fn_ssa vm`, `ssa_state_equiv vm s_orig s_ssa`, and `run_function fuel fn s_orig = result`, then there exists `result_ssa` such that
`run_function fuel fn_ssa s_ssa = result_ssa` and `ssa_result_equiv vm result result_ssa`.

## Key Insights
1. `valid_ssa_transform_def` implies `wf_input_fn fn` and `wf_blocks_ssa_compatible vm`.
2. `wf_blocks_ssa_compatible` is equivalent to `blocks_ssa_compatible` and thus yields `fn_ssa_compatible` via `valid_ssa_transform_compatible`.
3. `run_function_ssa_equiv` gives SSA equivalence for the full function execution.

## Validated Assumptions (ALL must be VERIFIED)
- `valid_ssa_transform_def`: **VERIFIED** in `ssaWellFormed`.
- `valid_ssa_transform_compatible`: **VERIFIED** in `ssaFunction` (derives `fn_ssa_compatible`).
- `run_function_ssa_equiv`: **VERIFIED** (previous theorem).

## Preliminary Facts to Establish
1. `valid_ssa_transform_compatible`: converts `valid_ssa_transform` into `fn_ssa_compatible`.
2. `run_function_ssa_equiv`: provides `ssa_result_equiv` for executions.

## Proof Argument
Use `valid_ssa_transform_compatible` to obtain `fn_ssa_compatible vm fn fn_ssa` and the `wf_input_fn fn` precondition. Apply `run_function_ssa_equiv` to obtain
`ssa_result_equiv vm (run_function fuel fn s_orig) (run_function fuel fn_ssa s_ssa)`. Set `result_ssa = run_function fuel fn_ssa s_ssa` and conclude.

## Required Lemmas
- `valid_ssa_transform_compatible`.
- `run_function_ssa_equiv`.

## Potential Difficulties
- None beyond the validated preconditions.

---

## Theorem: ssa_construction_context_correct

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)
For a context `ctx`, if `fn` is a member of `ctx.ctx_functions`, `valid_ssa_transform fn fn_ssa vm`, `ssa_state_equiv vm s_orig s_ssa`, and `run_function fuel fn s_orig = result`, then there exists `result_ssa` such that `run_function fuel fn_ssa s_ssa = result_ssa` and `ssa_result_equiv vm result result_ssa`.

## Key Insights
1. This is an immediate corollary of `ssa_construction_correct` with `fn` chosen from the context.

## Validated Assumptions (ALL must be VERIFIED)
- Membership and naming conditions are explicit hypotheses.
- `ssa_construction_correct` is available as the main correctness theorem.

## Preliminary Facts to Establish
None beyond instantiating `ssa_construction_correct`.

## Proof Argument
Instantiate `ssa_construction_correct` with the chosen function `fn` and apply it directly.

## Required Lemmas
- `ssa_construction_correct`.

## Potential Difficulties
- None; this is a straightforward instantiation.

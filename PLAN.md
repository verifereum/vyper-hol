## simplify-cfg proof plan

### Progress
- Added simplify-cfg definitions, transforms, and initial correctness lemmas under `venom/passes/simplify_cfg/`.
- Fixed definition parsing issues in `scfgDefsScript.sml` and ancestor imports in `scfgCorrectScript.sml`.
- Added skeleton correctness theorems for simplify-cfg steps and overall relation (cheated for now).
- Proved `resolve_phi_replace_label`, `resolve_phi_remove_non_preds`, and updated
  `step_inst_simplify_phi_inst` to return `result_equiv_cfg` (error strings differ).
- Build now succeeds, but `scfgCorrectTheory` is still CHEATED (see below).

### High-level correctness argument (math, verified against defs)
- **Semantics basis.** `run_function` consumes **one fuel per block** and recurses
  when `run_block` returns `OK` with `vs_halted = F`. `state_equiv_cfg` ignores
  control fields (`vs_current_bb`, `vs_prev_bb`, `vs_inst_idx`) but equates all
  data/state fields. `result_equiv_cfg` equates `Error` results and requires
  `state_equiv_cfg` for `OK/Halt/Revert`.
- **Simplify-PHI core lemma.** If `MEM prev preds` and `resolve_phi prev ops = SOME val_op`,
  then `resolve_phi prev (phi_remove_non_preds preds ops) = SOME val_op` (proof by
  induction on `ops`). Therefore, for a PHI with `s.vs_prev_bb = SOME prev`, the
  PHI case of `step_inst` is preserved up to `result_equiv_cfg` by
  `simplify_phi_inst`. Non-PHI opcodes are unchanged by `simplify_phi_inst`.
- **Block-level preservation.** Mapping `simplify_phi_inst` over instructions
  preserves `get_instruction` at each index. Under the PHI lemma above for every
  executed PHI, `step_in_block` produces a `result_equiv_cfg` result and the same
  `is_term` flag, hence `run_block` is preserved (by induction on the run_block
  recursion).
- **Required well-formedness (missing from current statements).**
  1. **Terminator-last**: the executed terminator of a block is its last
     instruction. This is required so that `block_successors` (which uses
     `block_last_inst`) matches the successor chosen by `run_block`; otherwise
     `reachable_label` may disagree with actual execution.
  2. **Entry has no PHI**: if `s.vs_prev_bb = NONE` and entry has a PHI, then the
     original semantics errors (`phi at entry block`) while simplify-phi can
     rewrite it to `NOP/ASSIGN`, changing behavior.
  3. **PHI operands only mention actual predecessors (no duplicates)**: needed so
     `replace_label_fn` (label rewriting) does not introduce a duplicate label
     that changes which operand `resolve_phi` selects.
- **remove_unreachable_blocks.** Under terminator-last, any block reached by
  `run_function` is `reachable_label fn entry lbl`. Filtering preserves all
  reachable blocks and all reachable predecessor edges. Thus for any executed
  PHI in a kept block, its `prev` is in `pred_labels` of the filtered function,
  and simplify-phi preserves the step. Unreachable blocks are never executed.
- **merge_blocks.** With `block_last_jmp_to b_lbl a`, `pred_labels fn b_lbl = [a_lbl]`,
  and `block_has_no_phi b`, executing `a` then `b` is equivalent (up to control
  fields) to executing `a' = BUTLAST a ++ b`. The label rewrite
  `replace_label_fn b_lbl a_lbl` is semantics-preserving **only if** PHI operands
  do not already contain `Label a_lbl`. This follows from the PHI well-formedness
  assumption above. **Fuel caveat:** merging removes one block, so same-fuel
  equivalence can fail (original may run out of fuel when the merged version
  terminates). The correctness statement must be weakened to a fuel-insensitive
  termination equivalence (see “Current blocker”).
- **merge_jump.** With `jump_only_target b = SOME c` and `pred_labels fn b = [a]`,
  redirecting `a` to `c` is semantics-preserving **only if** `a` was not already
  a predecessor of `c`. Otherwise PHI nodes in `c` cannot distinguish the two
  incoming edges after rewriting `b` to `a`. This is a real counterexample to the
  current `merge_jump_correct` statement and must be excluded by an additional
  condition such as `~MEM c (block_successors a)` (or an equivalent PHI invariant).
- **simplify_cfg_step / simplify_cfg.** Once each step lemma is proved under the
  strengthened preconditions, use transitivity of the chosen equivalence and
  induction on `RTC simplify_cfg_step`.

### Cheats (to discharge)
- `step_in_block_simplify_phi` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `run_block_simplify_phi` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `remove_unreachable_blocks_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `merge_blocks_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `merge_jump_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `simplify_cfg_step_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `simplify_cfg_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.

### Next steps
1. Add explicit well-formedness predicates (terminator-last, entry no-PHI, PHI
   operands only mention preds / no duplicates) and update theorem statements.
2. Replace same-fuel correctness with a **fuel-insensitive equivalence**, e.g. a
   bidirectional termination relation: if one terminates for some fuel then the
   other terminates for some fuel with `result_equiv_cfg` on the terminating runs.
3. Strengthen `merge_jump_cond` (or its correctness theorem) to forbid the case
   where `a` is already a predecessor of the jump-only target.
4. Complete `step_in_block_simplify_phi` and `run_block_simplify_phi`, then prove
   the pass-level lemmas under the revised assumptions and rebuild.

### Current blockers (proof non-provable as stated)
1. **merge_jump_correct is false** without an extra safety hypothesis. Example:
   `a` ends with `JNZ [cond; Label b; Label c]`, `b` is `[JMP (Label c)]`,
   `pred_labels fn b = [a]`, and `c` has PHI operands
   `[Label a; Var x; Label b; Var y]`. Original execution distinguishes `a` vs
   `b`; after merge-jump both branches set `vs_prev_bb = a`, changing the chosen
   PHI value. This requires adding `~MEM c (block_successors a)` (or equivalent).
2. **Same-fuel equivalence is too strong** for `merge_blocks` and `merge_jump`.
   `run_function` consumes one fuel per block. Merging removes a block, so for a
   small fuel `n` it is possible that `run_function n fn s` errors (out of fuel)
   while `run_function n fn' s` terminates. Thus the current theorems with a
   fixed `fuel` cannot be proved and must be weakened to a fuel-insensitive
   termination equivalence.
3. **remove_unreachable_blocks needs CFG/PHI well-formedness.** If a block’s
   terminator is not last, `block_successors` can diverge from actual execution,
   so reachable blocks may be incorrectly removed. If the entry block contains a
   PHI, simplify-phi can change an “entry PHI” error into `NOP/ASSIGN`.

## simplify-cfg proof plan

### Progress
- Split simplify-cfg correctness into three theories to keep files <500 LOC:
  `scfgEquivScript.sml` (equivalence/state lemmas), `scfgPhiCorrectScript.sml`
  (PHI/simplify-phi proofs), and `scfgCorrectScript.sml` (pass-level proofs).
- Proved PHI/simplify-phi lemmas: `resolve_phi_vals_not_label`,
  `resolve_phi_replace_label`, `simplify_phi_inst_is_terminator`,
  `step_in_block_simplify_phi`, `run_block_simplify_phi`.
- Control-field preservation helpers for non-terminators are in place
  (`step_inst_preserves_prev_bb`, `step_inst_preserves_current_bb`).
- Build succeeds; remaining CHEATs are only the pass-level theorems in
  `venom/passes/simplify_cfg/scfgCorrectScript.sml`.

### High-level correctness argument (math, verified against defs)
- **Semantics basis.** `run_function` consumes **one fuel per block** and recurses
  when `run_block` returns `OK` with `vs_halted = F`. `state_equiv_cfg` ignores
  control fields (`vs_current_bb`, `vs_prev_bb`, `vs_inst_idx`) but equates all
  data/state fields. `result_equiv_cfg` equates `Error` results and requires
  `state_equiv_cfg` for `OK/Halt/Revert`. `run_function_equiv_cfg` is a
  bidirectional termination equivalence: any terminating fuel on one side has a
  (possibly different) terminating fuel on the other with `result_equiv_cfg`.
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
- **Required well-formedness (captured by current statements).**
  1. **Terminator-last**: ensured by `cfg_wf` via `block_terminator_last`.
  2. **Entry has no PHI**: ensured by `phi_fn_wf` (`block_has_no_phi` on entry).
  3. **PHI operands only mention actual predecessors**: ensured by
     `phi_fn_wf`/`phi_inst_wf` via `phi_ops_all_preds` and `phi_ops_complete`.
     The remaining duplicate-label hazard is handled structurally: `merge_blocks`
     requires `a` to end in a direct `JMP b`, so `a` has no other successors, and
     `merge_jump_cond` excludes `c` from `block_successors a`.
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
- `remove_unreachable_blocks_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `merge_blocks_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `merge_jump_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `simplify_cfg_step_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `simplify_cfg_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.

### Next steps
1. Prove `remove_unreachable_blocks_correct` using `cfg_wf` to align
   `reachable_label` with actual execution and the `run_block_simplify_phi`
   lemma for PHI cleanup on reachable blocks.
2. Prove `merge_blocks_correct` and `merge_jump_correct` using the new
   `resolve_phi_replace_label` lemma and the strengthened `merge_jump_cond`.
3. Finish `simplify_cfg_step_correct` and `simplify_cfg_correct` by composing
   the step lemmas with transitivity of `run_function_equiv_cfg`.

### Current blockers (none known)
All remaining statements align with the strengthened preconditions and
`run_function_equiv_cfg`. The remaining work is proof engineering.

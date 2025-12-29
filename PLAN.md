## simplify-cfg proof plan

### Progress
- Added simplify-cfg definitions, transforms, and initial correctness lemmas under `venom/passes/simplify_cfg/`.
- Fixed definition parsing issues in `scfgDefsScript.sml` and ancestor imports in `scfgCorrectScript.sml`.
- Added skeleton correctness theorems for simplify-cfg steps and overall relation (cheated for now).
- Build now succeeds, but `scfgCorrectTheory` is CHEATED (see below).

### High-level correctness argument (math, verified against defs)
- Goal: for `s.vs_current_bb = entry_label fn` and `s.vs_prev_bb = NONE`, show
  `result_equiv_cfg (run_function fuel fn s) (run_function fuel fn' s)` for each
  simplify-cfg step, then lift to `RTC simplify_cfg_step`.
- `state_equiv_cfg` ignores control labels/indices (`vs_current_bb`, `vs_prev_bb`,
  `vs_inst_idx`), so we only need to preserve vars/memory/storage/contexts.
- **Simplify-PHI correctness core.** For PHI instructions with `s.vs_prev_bb = SOME prev`
  and `MEM prev preds`, removing non-pred operands preserves `resolve_phi prev`.
  This is a direct induction on `phi_remove_non_preds_def`; no extra assumptions
  are needed because only non-matching labels are removed and list order is kept.
  From this, `simplify_phi_inst` preserves `step_inst` in the PHI case (ASSIGN
  case uses the same operand), and is identity for non-PHI opcodes.
- **Block-level preservation.** If every PHI step at index `idx` satisfies the
  above condition (prev in `preds`), then `step_in_block` and `run_block` are
  unchanged after `simplify_phi_block`. This uses the fact that instruction
  lists are mapped pointwise and `get_instruction` is index-stable under MAP.
- **remove_unreachable_blocks.** Let `entry = entry_label fn`. Any block reached
  by `run_function` is `reachable_label fn entry lbl` because each `jump_to` uses
  a successor edge (`cfg_edge` via `block_successors`). Filtering to reachable
  blocks keeps all blocks ever executed. For any execution edge `prev -> lbl`,
  both labels are reachable, so `prev` remains in `pred_labels fn' lbl` after
  filtering; therefore `simplify_phi_block (pred_labels fn' lbl)` preserves
  block semantics by the PHI lemma. Unreachable blocks are never executed.
- **merge_blocks.** With `block_last_jmp_to b_lbl a` and `pred_labels fn b_lbl = [a_lbl]`,
  executing `a` then `b` is equivalent (up to ignored control labels) to executing
  `a' = BUTLAST a ++ b`: the removed `JMP` has no data effects; `b` has no PHI so
  no dependence on `vs_prev_bb` inside `b`. The only semantic difference is the
  `vs_prev_bb` seen by successors of `b`; `replace_label_fn b_lbl a_lbl` corrects
  this by rewriting labels. To make `resolve_phi` stable under this rewrite, we
  need **no pre-existing `Label a_lbl` in PHI operands that also mention `b_lbl`**.
  This is ensured if PHI operand labels are confined to actual CFG predecessors
  (and `a` has only successor `b`), or we must add a well-formedness assumption.
- **merge_jump.** With `jump_only_target b = SOME c` and `pred_labels fn b = [a]`,
  executing `a -> b -> c` is equivalent to `a -> c` because `b` is a single `JMP`.
  The only semantic change is `vs_prev_bb` at `c` (from `b` to `a`), so
  `replace_phi_in_block b_lbl a_lbl` must preserve `resolve_phi`. This again
  requires that PHI operands do not already include `Label a_lbl` alongside
  `Label b_lbl` (or that both entries are semantically equal). If this cannot be
  derived from existing IR well-formedness, the correctness theorem must be
  strengthened with this hypothesis.
- **simplify_cfg_step / simplify_cfg.** Case-split on the step definition and
  apply the corresponding lemma. Then use transitivity of `result_equiv_cfg` and
  induction on `RTC` for the full pass.

### Cheats (to discharge)
- `resolve_phi_replace_label` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `resolve_phi_remove_non_preds` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `step_inst_simplify_phi_inst` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `step_in_block_simplify_phi` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `run_block_simplify_phi` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `remove_unreachable_blocks_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `merge_blocks_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `merge_jump_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `simplify_cfg_step_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.
- `simplify_cfg_correct` in `venom/passes/simplify_cfg/scfgCorrectScript.sml`.

### Next steps
1. Decide and formalize the needed PHI well-formedness assumption for label
   rewrites (`~MEM (Label new) ops` or equivalent), and update theorem statements.
2. Prove `resolve_phi_remove_non_preds` and `resolve_phi_replace_label` under the
   finalized assumptions.
3. Use those lemmas to finish `step_inst_simplify_phi_inst`,
   `step_in_block_simplify_phi`, and `run_block_simplify_phi`.
4. Prove the simplify-cfg skeletons (`remove_unreachable_blocks_correct`,
   `merge_blocks_correct`, `merge_jump_correct`, `simplify_cfg_step_correct`,
   `simplify_cfg_correct`) and remove CHEATs.
5. Rebuild and ensure no CHEAT warnings.

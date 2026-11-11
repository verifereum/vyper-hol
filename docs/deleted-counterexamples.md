# Counterexamples behind dropped statements

Several statements in the analysis and memory-safety proofs were found false and were dropped or restated. The theories that checked those counterexamples are gone; this note keeps what each one showed.

## `step_preserves_safety` doesn't hold for every function

`step_preserves_safety fn roots` says that every non-terminator, non-external-call instruction of `fn` preserves `alloca_safe_access` and `ptrs_in_alloca_bounds`. It is a per-function premise, and some functions break it: a pointer-preserving `ADD` with an unbounded operand. With `ptr = 0w` inside an alloca `[0, 64)` and `k = 9999w`, `ADD [Var "ptr"; Var "k"]` yields `9999w`, outside every alloca, so `ptrs_in_alloca_bounds` fails afterwards. `alloca_safe_access` still holds there, vacuously, because `9999w` lies in no alloca region. Results that take `step_preserves_safety` as a hypothesis stay valid, but they say nothing about a lowered function until something proves that function satisfies the premise, or a weaker contract replaces it.

## `bp_ptrs_bounded` doesn't imply `alloca_safe_access`

The bridge `bp_ptrs_bounded_imp_alloca_safe_access` is false. `alloca_safe_access` bounds the runtime access size (`eval_operand sz_op s = SOME sz_val ⇒ w2n w + w2n sz_val ≤ off + asz`), while `bp_ptrs_bounded` only checks compile-time structure: for a variable-sized operation `bp_segment_from_ops` gives `ml_size = NONE`, and `memloc_within_alloca` with `ml_size = NONE` is trivially true. With the state unconstrained, the size variable can take any value and break the bound.

## Memory SSA

- `mem_ssa_reaching_acyclic` is false without `cfg = cfg_analyze fn` and `dom = dom_analyze cfg fn`: a cyclic immediate-dominator map creates reaching cycles. `memSSAProofs.mem_ssa_reaching_acyclic` carries those premises.
- `mem_ssa_clobber_sound` was false in two ways. A `MnPhi` access node satisfies `completely_contains` trivially through `ml_empty`, so the access must not be a `MnPhi`. And a later definition in the same block dominates the access without being on its reaching chain, so the statement uses `strict_dominates` rather than `dominates`. `memSSAProofs.mem_ssa_clobber_sound` has both fixes.
- `mem_ssa_phi_at_frontier` is false because the pass's last phase removes redundant phis, which removes the frontier witness. It was dropped; nothing used it.

## Stack order

`so_analyze_block` tracks which operands the stack layout needs, not liveness. A variable defined and consumed inside a block is popped from the simulated stack, but if a successor needs it, the terminator adds it back to `needed`, although its definition makes it dead at block entry. So `so_needed_are_live` is false without `single_use_form`. An earlier, stronger `so_get_stack_sound` was false even with `single_use_form`: the `ASSIGN` handler adds a variable to `needed` when it is live at the next instruction, and `single_use_form` doesn't count `ASSIGN` uses. The current `stackOrderProofs.so_get_stack_sound` is the weaker statement.

## `MCOPY` and alloca relocation

The original `MCOPY` case of the alloca-remap preservation proof (`mcopy_preserves_remap`) was false: a zero-padded copy materializes different memory lengths in the original and the relocated state, so no successor state stays related by `alloca_remap_rel`, although every antecedent of the old helper held.

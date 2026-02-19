# CFG Analysis Parity Review (vyper-hol vs Vyper)

## Scope
This document compares Vyper’s CFG analysis with the HOL implementation in
`venom/analysis/cfgAnalysisScript.sml`. It focuses on behavioral parity and
possible divergence points.

## Sources
**Vyper**
- `vyper/venom/analysis/cfg.py`
- `vyper/venom/function.py` (entry semantics)
- `vyper/venom/basicblock.py` (out_bbs construction)

**HOL**
- `venom/analysis/cfgAnalysisScript.sml`
- `venom/venomInstScript.sml` (entry_block, get_successors)

## High-level behavior
Both implementations:
- Build successor and predecessor maps for every block.
- Run DFS from the entry block to compute:
  - postorder list
  - preorder list
  - reachable set
- Expose helper accessors for succs/preds/reachable.

## Detailed parity review

### 1) Entry block selection
**Vyper:** `IRFunction.entry` is the first basic block in insertion order.  
**HOL:** `entry_block fn = SOME (HD fn.fn_blocks)` (when nonempty).

**Potential divergence:** If `fn.fn_blocks` is not in insertion order, entry may
diverge. In Vyper, entry is always the first block created.

### 2) Successor order (critical for DFS order)
**Vyper:**
- `IRInstruction.get_label_operands()` yields labels in **operand order**.
- `IRBasicBlock.out_bbs` preserves that order.
- `cfg_out` iterates `reversed(bb.out_bbs)`, so final order is **reverse of
  terminator label operand order**.

**HOL:**
- `get_successors` extracts labels in **operand order** from `inst_operands`.
- `bb_succs` applies `REVERSE` to that list, so final order is also **reverse of
  terminator label operand order**.

**Conclusion:** Successor order matches Vyper *if terminator operand order
matches Vyper’s IR*. For example:
- `JNZ` operands are `[cond, if_nonzero, if_zero]` in Vyper and HOL.
- After reversal, successors are `[if_zero, if_nonzero]` in both.

If we want a formal guarantee, we should add a small lemma in `venomInstScript.sml`
stating that terminator operand order is fixed by the IR definition and that
`get_successors` preserves operand order.

### 3) Predecessor order
**Vyper:** Predecessors are stored in `OrderedSet`, preserving insertion order.  
**HOL:** Predecessors are list-backed with `ordset_add` (cons) plus `FOLDR`. This
preserves per-block order but reverses **global** order relative to block iteration.

**Potential divergence:** If any analysis relies on predecessor order, HOL may
diverge. Most analyses treat preds as sets; if order matters, we should align
with Vyper’s insertion order (e.g., append instead of cons).

### 4) Reachability
**Vyper:** `_reachable` is a map `bb -> bool`, set during DFS.  
**HOL:** `cfg_reachable` is a map `label -> bool` built from the DFS visited set.

**Potential divergence:** None for semantics; the only risk is duplicate labels.

### 5) DFS preorder / postorder
**Vyper:**
- Preorder: yielded by a recursive DFS generator.
- Postorder: `_dfs` ordered set where nodes are added after exploring succs.

**HOL:**
- `dfs_pre_walk` mirrors recursive preorder.
- `dfs_post_walk` mirrors recursive postorder (append after exploring succs).

**Potential divergence:** DFS order depends on successor order (see §2).

### 6) Unreachable blocks
Both implementations only traverse from entry. Unreachable blocks appear in
succ/pred maps but not in DFS lists or reachable set.

### 7) Label domain / uniqueness
**Vyper:** Blocks are objects; duplicate labels are disallowed by construction.  
**HOL:** Blocks are keyed by `bb_label` strings; duplicates collapse map entries.

**Potential divergence:** If duplicate labels exist, HOL behavior diverges.
This should be an explicit IR well-formedness predicate, e.g. `labels_unique`
over `MAP bb_label fn.fn_blocks` in `venom/venomInstScript.sml` (or a new
`venomWfScript.sml`).

### 8) Mutation / invalidation hooks
**Vyper:** CFG supports add/remove edges and invalidation hooks.  
**HOL:** analysis is pure; no mutation APIs.

**Potential divergence:** None for static analysis results. If we later model
mutable caches, we may need explicit invalidation behavior.

## Summary of parity
**Matches Vyper**
- Entry semantics (first block).
- Successor order (reverse of terminator label operand order).
- DFS preorder/postorder semantics (reachable-only traversal).
- Reachability computed from DFS.
- `cfg_is_normalized` predicate mirrors Vyper’s check.

**Potential divergence**
- Predecessor ordering (list order may differ).
- Label uniqueness assumptions (HOL uses strings).
- Successor order relies on terminator operand order; if the IR encoding differs,
  traversal order diverges.

If strict order parity is required, we should explicitly state/prove that
terminator operand order is fixed, and adjust predecessor ordering to match Vyper.

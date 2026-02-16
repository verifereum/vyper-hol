CFG Analysis Parity Notes
=========================

This note captures the disparities found between:

- this branch’s HOL CFG (`venom/analysis/cfgAnalysisScript.sml`)
- the compiler-pass-definitions branch (`origin/compiler-pass-definitions`)
- the Python Vyper implementation (`vyper/venom/analysis/cfg.py`)

It is intentionally concrete so we can track parity changes.

Disparities vs Vyper (Python)
-----------------------------

1) Successor order
- Vyper inserts successors in *reverse* order of `bb.out_bbs`:
  `for next_bb in reversed(bb.out_bbs)`
- Our branch previously used successors in the direct order.
- compiler-pass-definitions also reverses.

Impact: DFS and worklist order differ; analyses like liveness can converge to
the same fixpoint but do not mirror Vyper’s traversal order.

2) DFS postorder list orientation
- Vyper’s DFS postorder `_dfs` preserves postorder (visit succs, then add bb).
- Our branch previously built `cfg_dfs_post` by consing on EXIT, which produced
  the reverse of Vyper’s order.
- compiler-pass-definitions builds postorder with `orders ++ [lbl]`, matching Vyper.

3) Missing DFS preorder
- Vyper exposes `dfs_pre_walk` (used by other analyses).
- compiler-pass-definitions contains `dfs_pre`.
- Our branch originally had no preorder list.

4) Reachability shape
- Vyper stores `reachable: bb -> bool`.
- compiler-pass-definitions stores `reachable: label -> bool`.
- Our branch stored `cfg_reachable` as a list of labels (membership test only).

5) Entry block choice
- Vyper uses `function.entry`.
- compiler-pass-definitions uses the first block `bb :: _`.
- Our branch uses `entry_block fn` (needs to be equivalent to Vyper’s entry).

6) Dynamic update hooks
- Vyper supports `add_cfg_in/out`, `remove_cfg_in/out`, `invalidate`.
- HOL analysis is pure and has no update/invalidate API (expected), but this is
  a semantic difference if we later model in-place CFG mutation.

Status / Actions in this branch
-------------------------------

- Successor order reversed to match Vyper.
- DFS postorder switched to the recursive, append-based form (postorder).
- DFS preorder added.
- Reachability now modeled as a map `label -> bool`.
- Entry selection now uses the *first block* (`HD fn.fn_blocks`), matching
  Vyper’s `IRFunction.entry` which is the first basic block in insertion order.
- Added `cfg_is_normalized` predicate (mirrors Vyper’s `is_normalized` check).
- Entry still uses `entry_block fn` (should be checked to equal Vyper entry).

Remaining differences to consider
---------------------------------

- Optional dynamic-update APIs only if we decide to model in-place mutation.
- If `fn_name` differs from the entry block label, that is allowed (but then
  `fn_wf_entry` does not hold). We do not rely on that invariant for entry.

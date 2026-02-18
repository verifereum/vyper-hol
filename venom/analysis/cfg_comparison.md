CFG Analysis Parity Notes (Vyper vs HOL)
========================================

This note compares the Vyper CFG analysis with the HOL CFG analysis in
`venom/analysis/cfgAnalysisScript.sml`. We intentionally ignore the
compiler-pass-definitions branch.

Vyper (Python) reference
------------------------

Source: `vyper/venom/analysis/cfg.py`

Key behaviors:
- Successor order: `cfg_out` is populated using `reversed(bb.out_bbs)`.
- DFS postorder: visit successors first, then add the block to `_dfs`.
- DFS preorder: yielded by a separate recursive walk.
- Reachability: per-block boolean map.
- Entry: `IRFunction.entry` is the first block in insertion order.
- Optional APIs: add/remove edges and invalidation hooks.

HOL implementation (this branch)
--------------------------------

Location: `venom/analysis/cfgAnalysisScript.sml`

Parity summary:
- Successor order matches Vyper (reverse order).
- DFS postorder matches Vyper (append after visiting successors).
- DFS preorder is computed explicitly.
- Reachability is stored as `label -> bool` map.
- Entry is `HD fn.fn_blocks` (first block), matching `IRFunction.entry`.
- We provide `cfg_is_normalized` predicate (equivalent to Vyper’s check).

Known differences / non-goals
-----------------------------

- We do not implement in-place mutation hooks (`add_cfg_in/out`, `remove_cfg_in/out`)
  or invalidation; HOL analysis is pure. If we later model a mutable analysis cache,
  we may add these APIs, but semantics of the analysis output already match Vyper.

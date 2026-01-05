# PROOF_DESIGN: PHI Insertion for make_ssa

This document presents the proof plan for PHI insertion in SSA construction, following the Vyper implementation in `vyper/venom/passes/make_ssa.py`.

## Reference Implementation Summary

From `make_ssa.py`:
```python
def run_pass(self):
    self._add_phi_nodes()      # Phase 1: Insert PHIs at dominance frontiers
    self._rename_vars(entry)   # Phase 2: Rename variables (already verified)
    self._remove_degenerate_phis(entry)  # Phase 3: Clean up
```

Key analyses used:
- **CFGAnalysis**: `cfg_in(bb)` (predecessors), `cfg_out(bb)` (successors)
- **DominatorTreeAnalysis**: `dominators`, `immediate_dominators`, `dominated`, `dominator_frontiers`
- **LivenessAnalysis**: `liveness_in_vars(bb)` - for pruning unnecessary PHIs

---

## Part 1: CFG Computation

### Definitions

```sml
(* Predecessor map: block label -> list of predecessor labels *)
Definition compute_cfg_in_def:
  compute_cfg_in fn =
    FOLDR (λbb acc.
      let succs = get_block_successors bb in
      FOLDR (λsucc acc'.
        let preds = case FLOOKUP acc' succ of SOME ps => ps | NONE => [] in
        acc' |+ (succ, bb.bb_label :: preds)
      ) acc succs
    ) FEMPTY fn.fn_blocks
End

(* Successor map: block label -> list of successor labels *)
Definition compute_cfg_out_def:
  compute_cfg_out fn =
    FOLDR (λbb acc.
      acc |+ (bb.bb_label, get_block_successors bb)
    ) FEMPTY fn.fn_blocks
End

(* Get successors of a basic block from its terminator *)
Definition get_block_successors_def:
  get_block_successors bb =
    case get_terminator bb of
      NONE => []
    | SOME term => get_successors term
End
```

### Theorem: cfg_in_cfg_out_consistent

**Verdict: PROVABLE**

**Goal**: `b IN cfg_out(a) <=> a IN cfg_in(b)`

**Proof**: Direct from construction - we add `a` to `cfg_in(b)` exactly when `b` is in `get_block_successors(a)`.

---

## Part 2: Dominator Computation

### Definitions

Following the Vyper implementation (iterative dataflow):

```sml
(* Dominator set: all blocks that dominate a given block *)
Definition compute_dominators_def:
  compute_dominators cfg_in entry all_blocks =
    let init = (λbb. if bb = entry then {entry} else all_blocks) in
    iterate_until_fixed (λdoms.
      FUN_FMAP (λbb.
        if bb = entry then {entry}
        else
          let preds = cfg_in bb in
          if preds = {} then all_blocks
          else bb INSERT (BIGINTER (IMAGE doms preds))
      ) all_blocks
    ) init
End

(* Dominates relation *)
Definition dominates_def:
  dominates doms a b <=> a IN doms b
End

(* Strict dominance *)
Definition strictly_dominates_def:
  strictly_dominates doms a b <=> dominates doms a b /\ a <> b
End

(* Immediate dominator: the unique strict dominator closest to bb *)
Definition immediate_dominator_def:
  immediate_dominator doms bb =
    if bb = entry then NONE
    else
      let strict_doms = doms bb DELETE bb in
      (* idom is the one not strictly dominated by any other strict dominator *)
      SOME (THE_CHOICE (λd. !d'. d' IN strict_doms /\ d' <> d ==>
                              ~strictly_dominates doms d' d) strict_doms)
End

(* Dominance frontier: blocks where dominance of bb ends *)
Definition compute_dom_frontier_def:
  compute_dom_frontier cfg_in idom all_blocks =
    FUN_FMAP (λbb. {}) all_blocks |>
    (λdf.
      FOLDR (λbb df'.
        if CARD (cfg_in bb) <= 1 then df'
        else
          FOLDR (λpred df''.
            iterate_runner pred (idom bb) (λrunner df'''.
              df''' |+ (runner, bb INSERT (df''' runner))
            ) df''
          ) df' (cfg_in bb)
      ) df all_blocks)
End

(* Runner iteration for DF computation *)
Definition iterate_runner_def:
  iterate_runner runner target f acc =
    if runner = target then acc
    else iterate_runner (THE (idom runner)) target f (f runner acc)
End
```

### Theorem: dominators_correct

**Verdict: PROVABLE**

**Goal**: For all paths from entry to b, a appears on every path iff `dominates doms a b`.

**Key Insight**: The iterative algorithm computes the meet-over-all-paths solution. Each iteration refines the dominator sets until fixpoint.

**Proof Sketch**:
1. Show initialization is correct: entry dominates only itself, others conservatively have all blocks
2. Show each iteration preserves: `doms(b) = {b} ∪ ∩{doms(p) | p ∈ preds(b)}`
3. Show fixpoint implies correctness: if `a ∈ doms(b)`, then `a` is on all paths to `b`

### Theorem: dom_frontier_correct

**Verdict: PROVABLE**

**Goal**: `b IN dom_frontier(a) <=> (∃p. p IN cfg_in(b) /\ dominates doms a p) /\ ~strictly_dominates doms a b`

**Key Insight**: The runner algorithm walks up from each predecessor until hitting the idom, adding the join point to each runner's frontier.

---

## Part 3: PHI Placement

### Definitions

Following the Cytron et al. algorithm used in Vyper:

```sml
(* Definition sites for each variable *)
Definition compute_defs_def:
  compute_defs fn =
    FOLDR (λbb acc.
      FOLDR (λinst acc'.
        case inst.inst_outputs of
          [] => acc'
        | (v::_) =>
            let sites = case FLOOKUP acc' v of SOME s => s | NONE => {} in
            acc' |+ (v, bb.bb_label INSERT sites)
      ) acc bb.bb_instructions
    ) FEMPTY fn.fn_blocks
End

(* PHI placement worklist algorithm *)
Definition phi_placement_def:
  phi_placement df defs var =
    let init_work = case FLOOKUP defs var of SOME s => s | NONE => {} in
    iterate_worklist init_work {} (λbb (work, placed).
      let frontier = df bb in
      let new_sites = frontier DIFF placed in
      (work UNION new_sites, placed UNION new_sites)
    )
End

(* Insert PHI for variable at block *)
Definition insert_phi_def:
  insert_phi preds var bb next_id =
    let phi = mk_phi_inst next_id var preds var in
    (bb with bb_instructions := phi :: bb.bb_instructions, next_id + 1)
End

(* Insert all PHIs for all variables *)
Definition insert_all_phis_def:
  insert_all_phis df cfg_in defs live_in fn =
    let vars = FDOM defs in
    FOLDL (λ(fn', next_id) var.
      let sites = phi_placement df defs var in
      FOLDL (λ(fn'', id) site.
        (* Only insert if variable is live-in at site *)
        if var IN live_in site then
          let bb = lookup_block fn'' site in
          let preds = cfg_in site in
          let (bb', id') = insert_phi preds var bb id in
          (update_block fn'' bb', id')
        else (fn'', id)
      ) (fn', next_id) sites
    ) (fn, 0) vars
End
```

### Theorem: phi_placement_complete

**Verdict: PROVABLE**

**Goal**: After `insert_all_phis`, every join point where different definitions of `v` meet has a PHI for `v`.

**Key Insight**: The worklist algorithm computes the iterated dominance frontier. A PHI is needed at block B for variable v iff B is in DF+(def_sites(v)).

**Proof Sketch**:
1. Show worklist computes iterated DF: `phi_placement df defs v = DF+(defs v)`
2. Show DF+ is exactly where definitions meet: if two paths to B have different reaching definitions for v, then B is in DF+
3. Conclude: every meeting point gets a PHI

### Theorem: phi_operands_cover_predecessors

**Verdict: PROVABLE**

**Goal**: For every inserted PHI, `resolve_phi prev phi.inst_operands ≠ NONE` for all predecessors `prev`.

**Proof**: `mk_phi_operands preds var` creates a Label/Var pair for each predecessor. `resolve_phi` finds the matching label.

---

## Part 4: Combined Correctness

### Theorem: make_ssa_correct

**Verdict: PROVABLE (contingent on liveness correctness)**

**Unverified Assumptions**:
- Liveness analysis is correct: `live_in bb` contains exactly variables live at bb entry

**Goal**: For function `fn` with no unreachable blocks:
```
fn_ssa = insert_all_phis(...) |> rename_function
run_function fuel fn s_orig = result
ssa_state_equiv vm s_orig s_ssa
==>
∃result_ssa. run_function fuel fn_ssa s_ssa = result_ssa /\
             ssa_result_equiv vm result result_ssa
```

**Key Insights**:

1. **PHI semantics match variable flow**: At a join point, the PHI selects the value from the predecessor we came from. This is exactly the value the original variable would have had.

2. **Reaching definitions**: For each PHI operand corresponding to predecessor P, after renaming, the operand is the SSA name of the reaching definition through P.

3. **Compositionality**: PHI insertion preserves semantics (PHIs read and write same variable), then renaming preserves semantics (existing proof).

**Proof Argument**:

#### Step 1: PHI insertion alone preserves semantics

Before renaming, each inserted PHI has form: `v = PHI [p1: v, p2: v, ...]`

When executed:
- `resolve_phi prev_bb [(p1, v), (p2, v), ...]` returns `Var v`
- `eval_operand (Var v) s` returns `lookup_var v s`
- Result: `update_var v (lookup_var v s) s` - a no-op!

So PHI insertion alone doesn't change semantics (PHIs are identity operations).

#### Step 2: PHI insertion + renaming preserves semantics

After renaming:
- PHI becomes: `v:k = PHI [p1: v:i, p2: v:j, ...]`
- Each `v:i` is the SSA name of the reaching definition through that predecessor
- When we came from `p1`, `v:i` has the value that `v` would have had in the original

The renamed PHI correctly captures the merge semantics.

#### Step 3: Use existing renaming proof

The existing `ssa_construction_correct` proves renaming is correct, but assumes `no_phi_fn`.

**Gap to fill**: Extend renaming proof to handle PHIs. The key addition:
- PHI operands are renamed per-predecessor (not using current stack)
- PHI outputs are renamed like other definitions

### Theorem: make_ssa_produces_wf_ir

**Verdict: PROVABLE**

**Goal**: Output of make_ssa satisfies `wf_ir_fn` from phi_elimination.

**Properties to prove**:

1. **ssa_form**: Each SSA variable defined once
   - Renaming gives unique version to each definition
   - PHI outputs get unique versions

2. **phi_well_formed**: PHI operands are Label/Var pairs
   - `mk_phi_operands` produces this structure
   - Have `mk_phi_operands_well_formed` theorem

3. **phi_single_output**: Each PHI has one output
   - `mk_phi_inst` creates `inst_outputs = [out]`

4. **entry_no_phi**: Entry block has no PHIs
   - Entry has no predecessors
   - `cfg_in entry = {}`
   - Algorithm only places PHIs where `CARD (cfg_in bb) > 1`

5. **phi_operands_direct**: Need to show PHI operands map to DFG origins
   - After renaming, each operand is a specific SSA definition
   - This connects to `phi_single_origin` in phi_elimination

---

## Implementation Plan

### New Files

1. **mkSsaCfgScript.sml** (~200 LOC)
   - `compute_cfg_in`, `compute_cfg_out`
   - `get_block_successors`, `get_terminator`
   - CFG consistency lemmas

2. **mkSsaDominanceScript.sml** (~400 LOC)
   - `compute_dominators` (iterative fixpoint)
   - `immediate_dominator`
   - `compute_dom_frontier`
   - `dominates`, `strictly_dominates`
   - Dominance correctness lemmas

3. **mkSsaPhiPlaceScript.sml** (~300 LOC)
   - `compute_defs`
   - `phi_placement` (worklist algorithm)
   - `insert_phi`, `insert_all_phis`
   - Placement completeness lemmas

4. **mkSsaPhiCorrectScript.sml** (~400 LOC)
   - `make_ssa_correct` theorem
   - PHI semantics lemmas
   - Composition with renaming

### Modifications to Existing Files

1. **mkSsaBlockStepScript.sml**: Add PHI case to `step_inst_result_ssa_equiv`
2. **mkSsaWellFormedScript.sml**: Remove `no_phi_fn` requirement, add `wf_ir_fn` connection
3. **mkSsaFunctionScript.sml**: Update `run_function_ssa_equiv` for PHI support

---

## Estimated Complexity

| Component | LOC | Difficulty | Notes |
|-----------|-----|------------|-------|
| CFG computation | 200 | Low | Straightforward graph construction |
| Dominance computation | 400 | Medium | Fixpoint iteration, needs termination |
| Dominance frontier | 200 | Medium | Runner algorithm |
| PHI placement | 300 | Medium | Worklist algorithm |
| PHI correctness | 400 | High | Key semantic argument |
| wf_ir_fn connection | 200 | Medium | Structural properties |

Total: ~1700 new LOC

---

## Open Questions Resolved

1. **Dominance computation**: Implementing the iterative dataflow algorithm from Vyper
2. **Following Vyper**: Yes, following `make_ssa.py` exactly
3. **Multi-output**: Handle like Vyper - iterate over all outputs
4. **Unreachable blocks**: Assume none (Vyper has separate reachability analysis)
5. **wf_ir_fn connection**: Will prove as separate theorem `make_ssa_produces_wf_ir`

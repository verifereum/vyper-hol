# C1.5.3: concrete forwarding proof boundary

Diagnostic only; all proposed invariants below remain unproved.

## Actual scheduler and available induction interface

`dfs_state` holds ds_stack (DfsProcess/DfsEmit items), ds_output, and ds_visited (instruction IDs). `dfs_step` (dftDefsScript.sml:488) has these cases:

* Empty stack: identity.
* DfsEmit i: pop, append i to output. This is the only emission case.
* DfsProcess i already visited: pop. Visited does NOT mean emitted: an emit marker may still be pending.
* Pseudo process: mark visited and pop without output.
* Fresh nonpseudo: mark visited, push sorted dependency processes, then a DfsEmit marker, then previous stack tail. Optional flipping is attached to the marker; it preserves IDs but not necessarily operands/opcode for comparators.

`schedule_from_entries` is FUNPOW of dfs_step for (LENGTH bi + 1)^2 steps, initialized with MAP DfsProcess entries and empty output/visited. Standard natural-number induction on that iteration count is available; `dfs_run_fuel_eq_FUNPOW` connects the evaluator. No new DFS-specific induction principle is necessary.

Existing dftScheduleOrder infrastructure should be reused:

* dfs_cut_work (974): a process must be a member satisfying P on IDs, an emit must satisfy P on IDs.
* dfs_cut (984): either distinguished root already emitted with EVERY P before it, or all output satisfies P and stack splits into P-work, distinguished root marker, tail. Process-root alternative requires root unvisited; emit-root alternative matches root ID.
* dfs_cut_children (1023): dependency closure of P union root implies all pushed work satisfies P.
* dfs_cut_run (1140), schedule_cut_before (1175): lift transition invariant to FUNPOW and order.
* dft_root_cut_closed (1209): under unique IDs, eda_wf, eda_topo_compatible, earlier-source-ID/pseudo cut is dependency closed.
* schedule_root_cut_before (1251): an entry root precedes any later source instruction in final schedule, under the preceding wf/topological hypotheses and membership of the later ID.

These prove a one-sided root cut, not an ASSIGN-only interval. RETURNDATACOPY has memory effects and is not automatically the effect-free root in dft_block_suffix_root_order.

## Candidate interval invariant shape

For source `pre ++ [copy] ++ mids ++ [rev]` with EVERY ASSIGN mids, candidate output condition at a state st:

```
!a b middle.
 st.ds_output = a ++ [copy] ++ middle /\
 ~MEM rev.inst_id (MAP (\i. i.inst_id) st.ds_output) ==>
 EVERY (\i. i.inst_opcode = ASSIGN) middle
```

The condition alone is NOT inductive. At the point copy is emitted it also needs a stack-work classification: all emit items ahead of the distinguished REVERT marker must be ASSIGN; every process there must either already be visited with its emit safely before copy, or its entire unvisited dependency closure must consist of ASSIGNs. Pending emit and visited IDs must be tracked separately. The statement uses actual dfs_state projections and the same work/marker/tail decomposition as dfs_cut; a two-marker variant may be needed rather than a new scheduler.

Transition audit:

* Empty/visited/pseudo cases do not emit, but removing a visited process is safe only if its pending emit classification already holds.
* DfsEmit between endpoints is the critical case: marker classification must imply ASSIGN. A non-ASSIGN cannot be excluded by membership or permutation alone.
* Fresh DfsProcess in the interval pushes children: closure must exclude unvisited non-ASSIGN producers. Existing source-topological cut says dependencies are earlier, not already emitted. A stronger provenance/visited fact is missing.
* DFS siblings of the copy can remain on the stack. They must satisfy the interval classification before copy is emitted. Merely saying all dependencies of REVERT are visited is insufficient.
* Later entry roots are in the stack tail. One must establish REVERT is processed before any unsafe root can be emitted in the interval, or show such roots cannot exist using root source order/last terminator. This is not a consequence of closure of REVERT dependencies alone.

A source prefix non-ASSIGN used through an ASSIGN chain by REVERT must be visited AND emitted before copy; the producer computation probe exhibits that result but does not prove it. Independent earlier roots need a separate cut/order argument. These are missing general obligations, not assumptions justified by the examples.

## Alias boundary

same_after_assigns scans latest first, succeeds immediately on operand equality, and otherwise steps both operands through step_back_assign. Non-ASSIGN output clobbers give NONE. resolve_block_assigns handles the middle backwards and stops at non-copy definitions. Permuting mids alone is insufficient because ASSIGNs can cross the copy boundary.

The exact elementary extension statement already planned as C1.5.2 is appropriate:

```sml
!xs ys a b. same_after_assigns xs a b ==>
             same_after_assigns (xs ++ ys) a b
```

It appends OLDER instructions only. Structural induction on xs with operands generalized handles it; equality is the early-success case. It does not prove invariance under permutation or newer insertion. Full alias transport still needs unique SSA producer provenance and preservation of each relevant definition's position before its use; an invariant must relate the prefix evidence and the middle resolve result together. Do not replace syntactic equality by evaluated-value equality.

The accepted E0002 source remains the only computation test: literal unchanged, alias order [1;2;0;3;5;4;6], producer unchanged. No experiment is repeated here. Next strategist update should select a reusable two-marker cut interface and discharge its pending-work closure, or revise the approach if that closure fails for actual entry/dependency transitions.

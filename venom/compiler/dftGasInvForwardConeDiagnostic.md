# Actual emitted-cone forwarding cut diagnostic (C1.5.8)

Checked artifact: `dftGasInvForwardConeProbeScript.sml`.
Verification: `holbuild(targets=["dftGasInvForwardConeProbeTheory"])` passed at the default tactic timeout (TO_dft_ev_lowered_inv-20261105T171048Z_m2466_t001).

## Scope and notation

These are four finite SSA blocks, each tested with orders `[]` and `["p"]`. All have unique instruction IDs, non-pseudo definitions before uses, well-formed instructions and terminal REVERT (`inv_cone_ssa_shapes`). Source and concrete transformed `revert_forward_pair` are checked, not inferred from a block relation. These facts do **not** establish universal forwarding preservation.

At the first copy emission let `st` be the actual initialized FUNPOW state, `V = MAP inst_id st.ds_output`, and `P i` mean `i.inst_opcode = ASSIGN`. In the table `Pi` denotes DfsProcess of instruction i and `Ei` denotes DfsEmit. The front includes the copy. All eight cases satisfy `inv_closed bi order (dft_eda bi) V P`, output-ID visitation, and `EVERY (inv_work bi V P) work` for the exact stack `work ++ [DfsEmit rev]` (empty tail).

| Motif | First copy emitted at step | Emitted IDs V | Full front visited? | work, order [] | work, order [p] |
|---|---:|---|---|---|---|
| 0: front q := p used only by REVERT | 5 | [0,2] | false | P1 | P0,P1 |
| 1: separate multi-hop pointer and size aliases, before and after copy | 11 | [1,3,0,2,4] | true | P7,P6 | P0,P7,P6 |
| 2: unrelated ADD feeds unused-output entry ASSIGN | 9 | [0,1,2,4] | false | P3 | P2,P3 |
| 3: non-ASSIGN pointer/size producers and repeated Process work | 10 | [0,2,1,5] | false | P4,P3 | P0,P4,P3 |

The surviving marker is respectively E3, E8, E5, E6. There are no other pending Emits in these cut states. The nonempty order adds a repeated Process of an already emitted pointer producer (IDs 0,0,2,0 respectively). In motif 3 this is a non-ASSIGN ADD, and its safety comes from membership in V, not its opcode. Visited and emitted sets differ: for example motif 0 has visited IDs [0,2,3] but emitted IDs [0,2]; REVERT is visited with its Emit still pending.

The concrete schedules (both orders) have IDs:

- 0: [0,2,1,3]; target pair indices (1,3).
- 1: [1,3,0,2,4,7,5,6,8]; target pair indices (4,8).
- 2: [0,1,2,4,3,5]; target pair indices (3,5).
- 3: [0,2,1,5,4,3,6]; target pair indices (3,6).

Source pairs have indices (2,3), (4,8), (4,5), (5,6). Source ASSIGNs used only by REVERT can remain fresh at copy emission (motifs 0,2,3). Thus full-front visitation is not a valid general initialization interface; this is not a counterexample to the frozen task theorem.

## Proposed universal bridge obligations (unproved)

The useful producer contract would be: for an actual initialized traversal of a well-shaped concrete forwarding block, identify the copy-emission iteration and corresponding pending REVERT marker, and produce the existing `inv_cut` premises with V equal to the output IDs at that iteration. In detail:

1. **Actual traversal and endpoints.** Prove the relevant copy and REVERT occurrences are reached in the same DFS/entry traversal, with REVERT's Emit still pending below the work at copy emission (or separately handle the already-completed alternative). Establish correspondence with the concrete source instructions; operand flipping must not change these endpoints.
2. **Emitted-set provenance.** Output IDs are visited. Do not identify all visited instructions with emitted instructions: a visited ancestor may still have a pending Emit. Track pending markers explicitly.
3. **Fresh alias-cone closure.** For every fresh ASSIGN, each dependency is either already emitted or another ASSIGN (`inv_closed`). Forwarding alias chains should join the copy's operand chains before a fresh non-ASSIGN producer is required. This must cover both operand producers and EDA/order-induced dependencies; direct operand provenance alone is insufficient.
4. **Stack classification at the actual cut.** Every Process above REVERT's marker is an emitted instruction or an ASSIGN; every Emit there is an ASSIGN. Earlier entry roots can discharge unrelated non-ASSIGN cones (motif 2), while repeated Process work is allowed via membership in V (motif 3). No inference from source-position bounds or visitation alone proves the Emit clause.
5. **Alias comparison transport.** Independently prove the three `same_after_assigns` comparisons used by the concrete target forwarding pair. An ASSIGN moving before copy changes the available prefix, and the emitted-cone cut only controls the interval after copy. A joint alias-chain correspondence across the source and emitted prefixes is needed; the existing older-tail fact by itself is not this correspondence.

Once (1)--(4) are supplied at the actual consumer, `inv_cut_pending`, `inv_cut_assign_run` and `inv_cut_output` provide the ASSIGN-only scheduled interval. Item (5) is still required for the target `revert_forward_pair`. None of these universal producers follows from the finite checks. In particular, the tests do not settle whether the proposed emitted-V closure holds for all shape-permitted forwarding blocks or all orders.

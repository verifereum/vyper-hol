# Forwarding-cut initialization audit (C1.5.7)

This report is a diagnostic, **not** a general forwarding preservation proof.
Existing theories are unchanged. The new `dftGasInvForwardStackProbeTheory`
checks a concrete competing dependency and its intermediate Process/Emit stack.

## Actual cut and concrete trace

Write the source nonpseudo list as `front ++ mids ++ [rev]`, where `front`
ends in `copy`, `EVERY (\i. i.inst_opcode = ASSIGN) mids`, and `rev` is REVERT.
Let `st0` be the actual initialized scheduler state (entry_instructions, empty
output/visited), `step = dfs_step bi order (dft_eda bi) om T`, and `st` the state
**immediately after** the Emit of copy. All universal claims below about this
cut remain unproved unless explicitly attributed to an existing theorem.

The intended instantiation of the existing cut is

```
inv_cut bi (MAP inst_id front) (\i. i.inst_opcode = ASSIGN)
  st.ds_output rev st
```

Here `pre` is the actual emitted prefix INCLUDING copy, not the original `front`.
At initialization its middle is empty. `rev` is not flippable, so its Emit marker
contains the original instruction. The suffix must actually end in this REVERT;
no argument from a generic block permutation supplies the marker.

The new probe is source IDs/opcodes
`[0:ADD -> z; 1:RETURNDATACOPY(z,0,1); 2:ASSIGN z -> trash; 3:REVERT(z,1)]`.
The source forwarding pair is checked. Attempting to use the unrelated middle
assignment to pull ADD after copy does NOT break forwarding: the unused-output
ASSIGN is an entry before REVERT and causes ADD to be emitted first. Actual
entries are `[Process 2; Process 3]`. The checked output is `[0;2;1;3]`, and the
transformed forwarding pair is at positions 2 and 3.

`inv_competing_trace` checks these snapshots, with P/E denoting Process/Emit:

| n | stack top first | output IDs | visited IDs |
|---|---|---|---|
| 0 | P2 P3 | [] | [] |
| 1 | P0 E2 P3 | [] | [2] |
| 2 | E0 E2 P3 | [] | [0,2] |
| 3 | E2 P3 | [0] | [0,2] |
| 4 | P3 | [0,2] | [0,2] |
| 5 | P1 P0 E3 | [0,2] | [3,0,2] |
| 6 | P0 E1 P0 E3 | [0,2] | [1,3,0,2] |
| 7 | E1 P0 E3 | [0,2] | [1,3,0,2] |
| 8 | P0 E3 | [0,2,1] | [1,3,0,2] |
| 9 | E3 | [0,2,1] | [1,3,0,2] |
| 10 | [] | [0,2,1,3] | [1,3,0,2] |

Thus the cut is n=8: `work=[P0]`, `tail=[]`, V=[0,1]. The pending non-ASSIGN
Process 0 is safe **because visited**, not because it is ASSIGN. Its Emit was
already consumed at n=3. At n=6 copy and REVERT are both visited but un-emitted;
this explicitly refutes treating visited as synonymous with emitted. The direct
producer Process 0 is skipped twice. The example validates the concrete trace,
not a universal initialization theorem.

## Initialization table for existing C1.5.4--C1.5.6 boundaries

| Premise | Existing producer | What remains |
|---|---|---|
| `inv_closed bi order (dft_eda bi) V P` | `inv_closed_assign_suffix`, V=all front IDs | Requires distinct IDs, nonpseudo definitions before uses, ASSIGN suffix and REVERT endpoint. It does NOT establish V is visited at cut. |
| `inv_flip_closed P` | `inv_flip_closed_assign` | None for P=ASSIGN. Endpoint REVERT and copy are not flippable. |
| `st.ds_output = pre ++ []` and `EVERY P []` | Choose pre=actual output after copy | Need identify actual occurrence of copy and its index, uniqueness/no duplicate emission. |
| `st.ds_stack = work ++ [DfsEmit rev] ++ tail` | No existing universal producer here | Prove rev was processed and its marker survives until copy emits; requires actual entry/child traversal lineage, not just topological order. |
| `EVERY (inv_work bi V P) work` | No existing universal producer here | Every Emit in work must be ASSIGN. Every Process must be in bi and either in V or ASSIGN. Membership/provenance alone cannot exclude pending non-ASSIGN Emit. |
| `EVERY (\id. MEM id st.ds_visited) V` | No full-front producer | `inv_scheduler_eda_provenance` and `inv_scheduler_producer_provenance` supply this ONLY for actual direct deps/producers of an emitted instruction. They also exclude those IDs from pending Emit markers. They do not cover arbitrary front IDs. |
| Completed empty stack and occurrence of rev | scheduler completion/structural results | Connect dft_block's bounded final state to the particular cut's remaining FUNPOW steps. |

The C1.5.6 provenance conclusions are genuinely useful: for each dependency of
copy already emitted they give emitted, visited AND no pending Emit. But their
quantification is over dependencies. Full front contains instructions unrelated
to copy, so blanket full-front visitation cannot be obtained by instantiating
those theorems repeatedly. Source position inequalities alone do not identify
ancestors or the pending child order.

## Exact unproved bridge obligations

The following are HOL-shaped **unproved specifications**, not new assumptions:

1. Pending marker and output occurrence, for actual `st=FUNPOW step (SUC n) st0`
   when the n-th state has copy's Emit at its head:
   `?a work tail. st.ds_output = a ++ [copy] /\
      st.ds_stack = work ++ [DfsEmit rev] ++ tail`.
2. The V chosen by `inv_closed_assign_suffix` is all source-front IDs:
   `EVERY (\id. MEM id st.ds_visited) (MAP inst_id front)`.
   This needs an entry-root/alias-cone argument for front instructions that
   are not copy dependencies; it is not a consequence of the accepted helpers.
3. At the same cut:
   `EVERY (inv_work bi (MAP inst_id front) (\i. i.inst_opcode = ASSIGN)) work`.
   In particular a previously visited non-ASSIGN with a pending Emit in work
   must be excluded, not excused by visitation. `stack_pos_ordered` only says
   source positions above a marker are at most that marker's position. Since
   REVERT is last, that inequality alone permits every front opcode.
4. Suffix iteration and output:
   after the remaining steps, `?middle post.
     final.ds_output = a ++ [copy] ++ middle ++ [rev] ++ post /\ EVERY P middle`.
   This is supplied by inv_cut_assign_run and inv_cut_output ONCE 1--3 and
   closure have genuine producers. It is not an additional assumption to hide.
5. Alias projection: transport the original resolve_block_assigns comparisons
   and same_after_assigns evidence into `a` and `middle`, using SSA producer
   correspondence. `same_after_assigns_older_tail` (in dftGasInvAlias) only appends
   older instructions. It does not transport arbitrarily reordered newer
   definitions or justify moving ASSIGNs across copy on its own. The concrete
   trace has moved ASSIGN 2 from between endpoints to before copy, illustrating
   why original mids cannot be identified with final middle.

## Derivation diagram and diagnosis

```
actual copy-emission lineage + entry-root order + alias producer cone
   -> marker rev pending + V visited + work classification  [MISSING]
source suffix wf -> inv_closed_assign_suffix                [PROVED]
ASSIGN -> inv_flip_closed_assign                            [PROVED]
   -> inv_cut_pending -> inv_cut_assign_run -> inv_cut_output [PROVED conditionally]
   -> actual ASSIGN-only output interval                    [needs missing init]
SSA syntactic alias transport                               [MISSING]
   -> revert_forward_pair at concrete scheduled endpoints
```

A promising missing invariant would classify pending work by actual DFS lineage
and by the copy/revert operand alias cone, while accounting for earlier entry
roots. The trace shows why these are two different producers: the unused ASSIGN
root discharges its ADD dependency before rev's processing; the later repeated
ADD processes are safe only because their Emit has already happened. Another
conditional cut lemma would not establish either fact.

This diagnostic does not certify initialization universally. It gives the exact
failed producer boundary rather than claiming that the old dependency-provenance
interface establishes stack order. No checked counterexample to the frozen
lowered-memory theorem or to concrete forwarding preservation was found.

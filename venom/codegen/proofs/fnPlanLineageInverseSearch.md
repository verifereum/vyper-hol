# Inverse temporal realizability search ledger

Scope: C3.temporal_realizability. No frozen theorem/definition edits.

## Bounds and current cursor

PLAN limits: regular ASSIGN/ADD words of length <=4, cores of 18--20 names,
<=256 fully evaluated local candidates, <=2 successful-local native embedding
attempts. So far **five** fully evaluated arbitrary-core local candidates:
one ASSIGN/core19 and four width18 grammar words. **One** native embedding
attempt rejected at layout compatibility. The30-word enumerator is defined,
but stopped after four evaluations (not exhausted).
Do not count the reversed-layout diagnostic as another native candidate.
No old selective_fn/shadow_fn fixture is mutated.

## Checked local candidate (fnPlanLineageInverseProbe)

- ASSIGN a -> y, exit = y,b0,...,b15,t,x.
- Literal liveness_transfer gives entry = b0,...,b15,t,x,a.
- Core = a,b0,...,b15,x,t; residual prefix = x.
- a is at depth18, target window1. Actual reduce_depth_plan emits
  SWAP1,SPILL0,SWAP1,SPILL32. First selected cell is sole common x;
  second is b15. Old top t stays depth0, protected by window1; it is NOT
  the second spilled cell. This is checked in inverse_native_reduction_calls.
- Full lineage_regular_prepare has identical code on core and prefix::core,
  with identical resulting records except the preserved prefix. Common x
  remains absent and spilled at the preoptimistic phase.
- Output y is live, LAST exit is x, and optimistic_swap_plan emits no code
  on common state but nonempty code with residual prefix x. Each fact is
  EVAL-certified; this is a local obstruction, NOT a native counterexample.

## First native embedding attempt

inverse_fn is a ready marker-free diamond (inverse_fn_markers checked): entry defines the 19 names, left/right JMP to join. Join begins
with the local ASSIGN; suffix uses x,t,b15,...,b0,y, then STOP.

Checked readiness and actual analyzed lists:
- live_vars_at analyze join 0 = local entry list.
- live_vars_at analyze join 1 = local exit list.
- left JMP join targets = MAP Var local entry list.

First violated embedding constraint: join targets have a at depth0,
whereas the inverse local core requires a at depth18. x remains on the
common stack after preparation from that target layout. join_target_ops
uses MAP of input_vars_from, NOT REVERSE. The separate reversed-entry
probe is just another local diagnostic, not a native join model.

First attempted embedding is rejected by the necessary target-layout
constraint above. Under the refined PLAN, native origin/whole-function SOME
checks for this rejected layout are unnecessary and are not pursued.
Neither bounded negatives nor arbitrary-core discrepancy discharges/refutes
lineage_state_block_plan.

Verification: holbuild target fnPlanLineageInverseProbeTheory passed.

## Follow-up bounded grammar and evaluator checkpoint

`inverse_words` enumerates all 30 boolean words of lengths1--4. T means
ASSIGN previous->fresh; F means ADD(previous,1)->fresh. Outputs y0..y3
quotient fresh renamings. The candidate derives all intermediate literal
lists with `inverse_backwards` (FOLDR liveness_transfer), executes real
regular preparation/steps, and checks prefix framing and an active LAST-x
observation. Cores18--20 use15--17 fillers; grammar bounds are checked.

Four width18 words [T],[F],[T,T],[T,F] are fully evaluated positive;
including the pre-existing different-name core19 witness, five local
candidates are now fully evaluated. The next word [F,T] is NOT evaluated:
regular-step release_dead_spills unfolds fmap_to_alist to SET_TO_LIST of
{Var b14,Var x}; this is noncomputable with the empty/singleton rules.
The symbolic result grows on the next preparation and times out. The
30-case aggregate theorem was removed; no aggregate result is claimed.
The evaluator needs a checked release boundary rather than more EVAL
or a chosen enumeration order for SET_TO_LIST.

Native entry SOME also remains unchecked. Even after staged analysis
context reductions, reducing the actual block call within2.5s fails;
this is not a native negative. Provisional incomplete native definitions
and theorem were removed. Native attempt count remains1. No second
embedding attempted, no successful whole-function/origin certificate.

## Refined native-layout feasibility diagnostic (second/final attempt)

Stop arbitrary-core enumeration at five evaluated candidates per review.
For the remaining layout attempt, use four ADD(previous,1)->fresh steps
from the literal entry target MAP Var (backwards schedule exit), width19.
`inverse_layout_four_adds_obstruction` checks entry order is
b0,...,b15,t,x,a. At every actual regular preparation x is still on the
common stack and the spill map is empty. `inverse_layout_four_adds` checks
the prefix-sensitive-loss scan returns F. Thus this schedule fails the
necessary common-loss condition before any native function is constructed.
This is one extra layout-compatible local evaluation, making six fully
evaluated local candidates in total (five arbitrary-core, one canonical).
Two native-layout attempts have now been considered; only the first reached
an actual analyzed function, the second is rejected before function design.
No search exhaustion is claimed (30-word grammar was not completed), no
universal physical invariant is proved, and no native counterexample is
claimed. The bounded construction is inconclusive for the frozen theorem.
The exact first obstructions are: attempt1 needs a at depth18 but actual
analyzed target has a at depth0; attempt2 retains common x at all four
prequery phases, so cannot produce the unmatched loss interval.

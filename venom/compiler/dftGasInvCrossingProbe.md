# Relevant-observation crossing diagnostic (C1.4.7.1)

## Checked results

`dftGasInvCrossingProbeTheory` classifies **source-earlier instructions absent
from the target prefix**, at observations with possible memory ranges or INVOKE.
This is not a simulation theorem. Existing theories and frozen definitions are
unchanged.

* `inv_memory_observation_covers_ranges` checks the enumeration against both
  read and write range definitions, under `inst_shape_ok`. INVOKE is explicitly
  included despite its empty direct ranges; its setup is a relevant observation.
  DELEGATECALL/CREATE/CREATE2 are excluded by shape, not silently omitted.
* `inv_crossing_candidate_necessary` exposes the effect conflicts, root barrier
  and observation-terminator barrier implied by `~dft_must_order`. Its boolean
  argument is exactly whether predecessor outputs are empty. SSA dependencies
  are additional restrictions, not erased from the concrete schedule.
* `inv_invoke_cannot_cross_memory` rules out a potentially nonreturning INVOKE
  predecessor for **every** enumerated observation. No return witness is assumed.
* ASSERT, ASSERT_UNREACHABLE and INVALID are output-free barriers. `inst_wf`
  supplies their empty outputs in `inv_fallible_crossing_classification`.
* Exhaustive constructor classification leaves only NoFail or
  SSTORE/TSTORE/LOG. In particular RETURNDATACOPY is excluded. Runtime-error
  opcodes DELEGATECALL/CREATE/CREATE2 are excluded by shape.
* Concrete EVAL checks show SSTORE, TSTORE, LOG and ALLOCA can pass the
  state-free crossing test at MLOAD; RETURNDATACOPY cannot pass it at MLOAD
  or MSTORE. These checks are about the necessary candidate predicate, not
  assertions that arbitrary concrete DFT blocks actually reorder those pairs.
* `inv_crossed_predecessor_total` produces an actual oracle OK result at any
  fuel/context, assuming wellformed/shape, nonpseudo/nonterminator predecessor,
  the relevant observation and no must-order edge, nonstatic frame, and defined
  operands. NoFail uses the existing guarded list-step totality boundary and
  the oracle equation; GAS is proved directly for the fixed event value.
  ALLOCA is separately total from literal/single-output wellformedness, including
  both allocated and unallocated cases. SSTORE/TSTORE/LOG use the existing
  CanExHalt disjunction plus a checked nonstatic no-abort theorem. The disjunction
  alone is NOT counted as totality.

No further concrete abort-run policy is needed for this particular classification:
`dft_must_order` plus wellformedness and shape already excludes every problematic
fallible predecessor except the nonstatic-total trio. Concrete abort order remains
relevant to completed-run reflection and forwarding preservation elsewhere.

## Actual-prefix obligations still missing

| Needed at consumer | Candidate producer | Remaining gap |
|---|---|---|
| Original block body membership, relative order and unique IDs | block relation / head bubbles, SSA and block wellformedness | connect actual target cut to extraction certificate |
| Successful PHI prefix and initial remaining invariant | source/target identical pseudo prefix; existing list `dft_remaining_inv_initialized` | oracle-entry adapter with actual source post-PHI state, strict dominator variables and label bounds |
| Nonpseudo/nonterminator crossed predecessors | source nonpseudo body, terminator-last block wellformedness | carry these syntactic facts into each actual-prefix construction |
| Defined operands for crossed predecessor at the state where it is inserted | SSA producer/dominator availability plus labels | `dft_remaining_inv_ready` alone concerns a selected residual head; not automatically the newly executed original-order predecessor; prove the appropriate actual-state readiness transition |
| Nonstatic state at each insertion | initial `o1_run_state_ok`, setup_callee, step frame invariants | oracle-step preservation and call-return merge preservation; not assumed merely from initial state |
| Remaining-invariant preservation after oracle OK | existing list `dft_remaining_inv_step` proof structure | GAS event-specific update and INVOKE reflection/frame adapter, not an application of the list theorem as-is |
| Same live operands/effects at target observation | adjacent commutation with total predecessor and SSA restrictions | oracle exchange kernel plus a coherent asynchronous cut invariant |
| Return from transformed callee implies source return | finite transformed IntRet witness and fuel induction | returning-run reflection still absent; classification only excludes crossing a not-yet-executed call before a relevant observation |
| Source lowered observation projects to target | actual source prefix, range operands, initial FMP, concrete forwarding | establish actual reachability via proved prefix boundary; forwarding bridge remains independent |

## Interpretation

The old obstruction 'an arbitrary pure observation can cross a nonreturning call'
is avoided by restricting observations to memory and call setup. This diagnostic
provides a genuine success **producer** for missing predecessors once actual-state
readiness and nonstaticness are supplied. It does not produce those premises, does
not construct an original-order prefix, and does not initialize or preserve a
residual relation. Do not resume a conditional simulation without a design for
these producers. No counterexample to the frozen theorem has been found or claimed.

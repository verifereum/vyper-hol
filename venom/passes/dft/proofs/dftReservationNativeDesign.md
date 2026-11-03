# Shared reservation: native consumer audit (C3.2.18)

This is a diagnostic deliverable, not a proof of the proposed obligations below.
Neither frozen theorem is changed or discharged by this audit.

## Checked example

`dftReservationNativeProbeScript.sml` builds as `dftReservationNativeProbeTheory`.
The caller has GAS g; INVOKE callee on the source and INVOKE callee; GAS g on
the target. The common callee executes GAS cg; MSTORE 0 cg; JMP exit, then RET
in the exit block. The source list is **[29;11] at both budgets**, and the target
list is [11;29]. `reservation_probe_oracle` checks that the former represents
`dft_reserve_oracle 1 a` for the latter's zero-extended oracle a.

* `reservation_probe_small_fuel`: both native run_blocks executions at fuel 2
  give Error "out of fuel".
* `reservation_probe_large_fuel`: both executions at fuel 3 give the same
  IntRet value [29] and exactly the same final state, with empty gas list.
* `reservation_probe_call_reachable` and `reservation_probe_memory_reachable`:
  actual native raw_reachable facts for both contexts, including the interior
  MSTORE observation. These use the raw callee rule, not a returned-call premise.
* `reservation_probe_memory_observation`: the MSTORE observations have equal
  inst_mem_ranges and vs_initial_fmp.

Important limitation: the raw facts are not indexed by fuel 2. The small-fuel
error and these raw facts are separate checked claims; this fixture does NOT
prove a native fuel-indexed observation trace theorem. The raw derivation of
MSTORE has three rule applications (entry, callee, next). Its next step uses
fuel 0 because GAS is not a call. Neither list length nor that chosen step fuel
counts the enclosing block-entry budget. The fuel-2 execution enters the
callee's first block but cannot enter its exit block.

## Exact consumer at the native boundary

Use the following notation only in this report:

* O(xs,j,s) = `dft_open_materialize xs j s`.
* a is the zero-extended oracle represented by finite list xs through
  `dft_sparse_oracle a xs`.
* b = `dft_reserve_oracle q a`; ys is any finite representation satisfying
  `dft_sparse_oracle b ys`. The finite-support rotation lemmas permit such a
  representation. ys must be fixed outside every budget/observation quantifier.
* Initial(ctx,v) is v with prev_bb NONE, current_bb the entry label, and
  inst_idx 0. Entry resolution and unique block labels are required.

For the local swap, take **all** premises at lines 183-198 of
`dft_open_gas_call_diamond`: common pre/post, adjacent GAS/INVOKE, equal labels,
index LENGTH pre, singleton GAS output, decoded and resolved callee, operand
independence and output disjointness, evaluated args, successful setup, the
protected segment at the larger call budget B, no premature distinguished
return, terminal IntRet with counter q, and output arity agreement. The native
start states are O(ys,0,s) and O(xs,0,s); their nongas fields agree. The caller
blocks can be wrapped as in the checked fixture or supplied by a common
reachable caller-frontier hypothesis. The local theorem alone is not a root
context reachability theorem for differently scheduled callers.

The required terminal boundary is a reverse implication, for each of step,
block, and run: under oracle agreement, a `dft_open_*_segment ... r` must imply
`dft_open_result_eq (native_operation ...) r`. For example the exact run shape
is

```
!a xs ctx fn fuel s stack n r.
  (!j. a (n+j) = if n+j < LENGTH xs then EL (n+j) xs else 0w) /\
  dft_open_run_segment a xs ctx fn fuel s stack n r ==>
  dft_open_result_eq (run_blocks fuel ctx fn (O(xs,n,s))) r
```

Here xs denotes the global list, consistent with the existing segment
materialization convention, not the remaining suffix at n. Reverse step and
block boundaries use the same global-list premise.
Together with forward segments, these would consume the diamond's joined
caller state for native endpoints. Further post execution requires oracle
agreement after q+1 and ordinary boundary composition. Native endpoints are
related modulo gas lists; identical concrete tails are not required by ctx_sim.

For observations the native predicate required by mem_inv is precisely:

```
!fn inst st.
  raw_reachable target0 target_ctx fn inst st ==>
  ?fn_s inst_s ss.
    raw_reachable source0 source_ctx fn_s inst_s ss /\
    inst_mem_ranges inst_s ss = inst_mem_ranges inst st /\
    ss.vs_initial_fmp = st.vs_initial_fmp
```

For the bounded local experiment this implication must be restricted to
observations in the distinguished callee before it returns, obtained with a
root fuel f <= F; it cannot quantify over *all* raw_reachable observations and
claim they belong to that call. A precise certificate for that restriction is
an open prefix from the call's DftEnter configuration with the distinguished
caller still on the stack, active DftAt observation, and existential finite
length j. Its missing native interpretation is the raw equivalence in
`dftOpenMachineScript.sml` lines 202-228, with `observed = O(xs,n,ghost)`.
Use that equivalence at the resolved context root, not at an arbitrary callee
pretending it is the context entry. Caller reachability must be included in
the certificate. This both specifies the native predicate and exposes the
missing bridge rather than defining 'raw observation' to mean an open endpoint.

## What is available, and what is missing

1. E0018 forward segments translate native evaluation to first-hit open
   segments. They do not reflect arbitrary open segments back to native results.
2. E0020 protected prefixes transport observations with one fixed rotated
   oracle while n <= q. Saved callers may differ; active callee control/state
   and nested caller prefix agree. Materialization changes only gas lists,
   so inst_mem_ranges and initial_fmp of the active callee agree.
3. E0022's diamond joins the callers at one budget after a normal callee return.
   It has no theorem comparing protected traces at call budgets b <= B.
4. `fuel_mono` in venomExecProofs transports non-Error terminal results, not
   active observations or nonreturning call prefixes. It cannot fill (3).
5. `raw_reachable` next/block permit arbitrary successful step fuels; callee
   entry requires setup and entry, not successful return. Thus (ii) cannot
   follow merely from (i), even in a context with unique labels.

The specific missing fuel-prefix obligation is: for every target protected
prefix at call budget b <= B that reaches an active observation before the
distinguished return, there exists a prefix of the returning B-budget
protected segment with the same active function, instruction and nongas state,
the same occurrence counter n, and n <= q. Budgets stored in active control
and every saved frame may differ; instruction/control path and saved nongas
states must correspond. This statement has to restrict to actual prefixes,
not arbitrary raw derivations. The B-budget trace terminates in IntRet, so
smaller-budget out-of-fuel exits are excluded from observation matching but
all preceding observations must be retained. Reflection to native raw facts
is a separate obligation, not part of this prefix correspondence.

Proposed recursion invariant for that obligation: pair active fn/block/index
and all saved call sites, equal nongas states and equal read counters; paired
remaining budgets differ by the common added root fuel along matching active
call paths. Block entry decrements both; invocation inherits the current
budget; return restores the saved budget. Stop at the first fuel-exhaustion
transition of the smaller machine. Distinguished caller opacity is maintained
separately by the reservation relation. A proof must check fatal/abort exits,
PHI entry, nested invocation and returning output binding, not only GAS.

## Bound and remaining bound gap

For a finite raw derivation D a candidate root budget can be computed from
its tree: entry needs at least 1; next/block need at least the chosen successful
step fuel plus the number of block entries along their active call ancestry;
callee entry adds one block entry without any return premise. One must also
allow the budgets needed to complete earlier INVOKEs in next premises. A safe
candidate is 1 + (number of raw rule nodes) + (sum of all numerical step fuels
appearing in D). This is a candidate, NOT a proved bound: it needs a decorated
raw induction plus non-Error step monotonicity to justify compatibility of all
successful subruns and restored caller budgets. Raw derivations omit the
internal derivation sizes of successful INVOKEs, so this is not by itself a
bound on machine step count. A step-count bound would additionally have to
include those finite evaluation derivations.

No uniform H(k) bounding source observation position in terms of target
position/family size has been established. In particular an arbitrary finite
raw derivation is NOT guaranteed to fit the F of one independently chosen
returning run. Either its observation is certified as a prefix at f <= F, or
a larger common budget is needed and its consistency with q must be proved.
No list-length bound on occurrences is valid after oracle exhaustion.

## Diagnostic conclusion

The fixed-list native fixture succeeds. The general consumer still lacks
reverse terminal boundaries, raw-prefix adequacy (with a decorated finite raw
bound), and cross-budget protected-prefix coherence. These are explicit
unproved obligations, not assumptions licensed for later use. Even proving
them would not prove DFT's global shared allocation, cross-context call
matching or H(k). Stop here for strategist review; no new adequacy machinery,
ledger or compactness construction is authorized by this diagnostic.

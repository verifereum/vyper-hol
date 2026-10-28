# Production indexed reclaim interface

`fmpReclaimDefs` now consumes the production static queries from
`fmpAliasDefs`. `fmp_reclaim_states infos fn` vetoes a failed base analysis;
there is no partially successful base environment. Current-state capture roots,
not a whole-function list of GETFMP outputs, control the veto.

## Original points and shared step

- `fmp_reclaim_step infos fn live env (label,index) inst state` returns
  `(restore option, successor state option)`.
- NONE is unreachable and produces `(NONE,NONE)`.
- At DALLOCA/JMP/JNZ/DJMP, or a resolved FMP-needing INVOKE, pop the maximal
  dead prefix of the newest-first stack. Any current capture veto prevents
  the entire pop. The restore is LAST popped, not the oldest of the full stack.
- Then DALLOCA pushes, GETFMP captures, SETFMP and publishing INVOKE clear.
  RETFMP/DRET do not clear. Unresolved INVOKE neither reclaims nor clears.
- The retained `frs_can_reclaim` flag is conservative bookkeeping for malformed
  DALLOCA output shapes; normal well-formed DALLOCA never sets it false.

The generic dataflow callback has no original index, so a task-local forward
adapter passes `(label,index)` explicitly. It uses the same boundary join,
worklist, CFG edges and stable-fuel check as the former analysis. It does not
rewrite instruction ids. `fmp_fold_prestate_lookup` proves that the map at
index `idx+k` contains exactly the result of executing the TAKE k prefix.

## Candidates and checking

`fmp_scan_candidates` walks original instructions only, queries their analyzed
pre-state and calls the same step used by transfer. `fmp_scan_candidate_lookup`
characterizes entries, `fmp_scan_no_end_candidate` excludes the synthetic
endpoint, and `fmp_scan_unreachable` excludes unreachable regions.
`fmp_pop_at_certificate` exposes decomposition, deadness and maximality;
`fmp_pop_target_lowest` and `fmp_step_pop_effect` expose restore and successor.

`fmp_reclaim_entry_ok` recomputes the accepted analysis and requires the target
selected by that step at a strict in-block point. Its target predicate uses
that state's captures and the task-local allocation-identity query. The old
exit-block, whole-stack, dominance/derived-variable whitelist, and whole-function
capture restrictions are gone. `analyze_fmp_reclaims_target_checked` exposes
the resulting current-state certificate, not an operational safety claim.

`fmpIndexedProbe` evaluates the production step for all reclaim/effect boundary
classes, needs/publishing/unresolved invokes, partial pops, current derived
captures, joins, unreachable points and deliberately non-index instruction ids.
Its final probe runs the complete production bounded analysis on two blocks:
restores appear before the second DALLOCA and before JMP, and nowhere at STOP
or block end. The older `fmpReclaimProbe` remains reference investigation;
its obsolete approximation definitions have been moved into that probe theory.

## Limits

The static projection ordering limits documented in `fmpAliasInterface.md`
are unchanged. Bounded analysis may conservatively fail. These are static
certificates only: C1.4.3 must connect eligibility/live/capture facts with concrete
allocation intervals, and C1.5 must place emitted restores at original indices.
No whole-program execution equivalence or bytecode parity follows merely from
these builds. In particular the existing lowering's end-only emission is not
changed in C1.4.2; its repair belongs to C1.5.

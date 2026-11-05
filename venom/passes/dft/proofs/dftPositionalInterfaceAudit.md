# Positional edit interface audit (C3.6.41)

This is an interface report, not a proof of a unified orbit diamond or of
finite gas realization. Checked probes are in
`dftPositionalOrientationProbeScript.sml`.

## What extraction actually provides

`dftPositionalProvenanceScript.sml:124-151`,
`dft_pos_provenance_edge_extract`, provides positional bounds, the source
block equation `pre ++ [x;y] ++ post`, the edited context equation, two
common-original context facts, `~dft_must_order x y`, and non-pseudo and
non-terminator conditions on both instructions. Its exclusion is directional.
Static reversal (`dftPositionalOrientation`) reverses the context/runtime
identities, not this exclusion or a dynamic phase.

Below O means non-GAS, non-INVOKE ordinary instruction; using its totality
boundary additionally requires wf, no ALLOCA, no DELEGATECALL/CREATE/CREATE2,
and operand readiness. These conditions are NOT all conclusions of extraction.

## Pair/orientation matrix

| Source pair | Existing boundary | Readiness / residual interface | Outcome and account |
|---|---|---|---|
| O/O (either order) | `dft_ordinary_pair_event_segment`, `dft_original_sync_event_segment` in dftOrdinaryEventTrace:149,202 | Pair/environment, label readiness, sync; pair theorem requires operands for x at s, y after successful x, and y at s. Reverse use requires the reversed environment, not merely static reversal. | Success 2/2; first/second abort bounded by 3 with final stack clearing; endpoint sync or ordinary-stopped. Gas-event set equality and right-to-left memory/operand prefix cover. |
| GAS/O | `dft_mixed_gas_first_pair_segment`, dftGasOrdinaryTrace:775 | Single GAS output v, v absent from O operands/outputs, O outcome OK or Abort. Original environment + labels derive these via `dft_original_mixed_sync_segment`:881. | Success 2/2; abort 3/2. In abort the GAS-first side alone has event (gas,path++[(visit,id)]). Same abort code, states need not agree. Prefix memory cover remains. |
| O/GAS | `dft_mixed_gas_second_pair_segment`:825 | Same disjointness/outcome conditions, proved directly in this orientation. | Success 2/2; abort 2/3. Edited GAS-first side alone has event. This is NOT symmetric event-set equality. |
| GAS/GAS | `dft_gas_sync_event_segment`, dftGasEventTrace:67; positional `dft_pos_gas_segment_next`, dftPositionalGasSegment:510 | Singleton distinct outputs, empty operands and distinct ids for old event boundary. Positional boundary uses runtime-ready and gas phase. | Two successful updates at crossing (1/1 outside), equal occurrence count and event set; positional segment account supplies both memory directions. |
| O/INVOKE | `dft_original_pos_orbit_ready`, dftPositionalOrbitReadiness:7, followed by positional orbit segment closure | Needs original label readiness on O-first C, phase C D, ~must_order O call, no GAS/ALLOCA/pseudo/terminator, label bound on C. | Recursive phase/segments cover call execution, returns and nonreturns, not just successful native steps. Ordinary crossing has no GAS debt; segment account includes counts, events, both memory directions. |
| INVOKE/O | Checked `dft_reverse_ordinary_orbit_readiness_probe` | Reverse O-first context is D. Still requires ~must_order O call, D label readiness, reversed phase D C and D label bound. Extraction supplies only ~must_order call O. | Conditional reversed ordinary interface checks, but the residual premises are NOT discharged. No unified reverse simulation is certified. |
| GAS/INVOKE | `dft_pending_bounded_closed_retired`, dftPositionalPendingClosure:1607 | Runtime-ready, both original contexts, singleton GAS output disjoint from call operands/outputs, annotated aligned phase. No ordinary operand readiness is needed for GAS itself. | Positive 1..2 steps on each side, annotated phase retained, `pending_segment_account` and monotone retired ledger. Return, restore failure and abandonment handled. Event debt is directed. |
| INVOKE/GAS | Checked `dft_reverse_gas_call_closure_probe` | Runtime reversal suffices for context identities. Still needs disjoint GAS output and **reversed annotated aligned phase** in D C. | Same pending account in reversed orientation. This does not construct that phase from an arbitrary forward cut or prove zero unmatched readings. |
| INVOKE/INVOKE | Excluded | Checked `dft_no_invoke_invoke_edge_probe`: INVOKE effects force must_order in either orientation. | No such edge satisfies extraction. |

No claim that reverse ~must_order is false in the common-original setting:
its derivation, if needed, is an additional unproved obligation. Likewise
original-context compatibility alone is not an annotation/phase initialization
proof.

## Non-call stopping and observation validation

`dftLocalOrdinaryClosureScript.sml:7-27` (`dft_shaped_ordinary_outcome`)
excludes Error and Halt for a ready, shaped ordinary instruction: the only
outcomes are OK and Abort. This depends on all the listed shape exclusions.
Do not generalize it to arbitrary non-call instructions without readiness.
GAS oracle updates are total at the singleton-output boundary.

`dftOccurrenceOrdinaryStopScript.sml:7-61` separates an Abort instruction
step from the following stack-clearing step. This explains the length-3
segments; a pair's abort endpoint is not necessarily reached in two steps.
`dftGasOrdinaryTraceScript.sml:34-44` permits differing abort states and
counts; `dft_mixed_segment_events` (76-94) identifies the exact unmatched
GAS/address in either orientation, rather than declaring event equality.

`dft_ordinary_prefix_cover` in dftOccurrenceOrdinaryClosure:629-640 is
**one-directional**: each edited memory observation is matched by an original
observation, including operand equality, ranges and memory, with functions
related by a value-level edit map. In contrast `dft_pos_segment_account`
in dftPositionalSegment:9-33 requires count equality, event-set equality,
and both memory directions using positional function pairing. The former
does not by itself establish the latter. Mixed aborts specifically violate
the event equality expected by an unannotated positional account.

`dftBlockSimScript.sml:1191-1205` gas_pair_commute is only a successful
same-context native two-step statement with existential changed gas input.
It does not cover stopping, differing callees, all intermediate observations,
or uniform witnesses for divergent execution. Its statement can be used but
cannot replace the above missing interfaces. This audit does not edit it.

## Exact proposed non-call bounded-segment boundary

Use the following existing mixed interface as the minimum honest signature
(no new theorem is asserted here). Let E abbreviate
`dft_gas_edit_ctx q pre x y post C`, and F abbreviate
`dft_gas_edit_fn q pre x y post`:

```sml
dft_original_gas_ordinary_environment Corig C L q pre x y post /\
dft_original_label_ready C L c /\
dft_gas_ordinary_endpoint q pre x y post c d ==>
?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
  dft_gas_ordinary_endpoint q pre x y post
    (FUNPOW (dft_occ_oracle_next w C) k c)
    (FUNPOW (dft_occ_oracle_next w E) j d) /\
  dft_original_label_ready C L
    (FUNPOW (dft_occ_oracle_next w C) k c) /\
  dft_ordinary_prefix_cover F w C E c d k j /\
  dft_mixed_segment_events w C E x y c d k j
```

This is precisely `dft_original_mixed_endpoint_segment` (914-940) with E/F
abbreviated. The environment (17-31) includes original context, block layout,
pair class, directional exclusion, shape restrictions, reverse schedule
edges for every original block witness, and global label bounds. The endpoint
allows sync or same-code abort-stopped. Thus stopping and observations are
explicit, not inferred from a successful diamond. The O/O counterpart is
`dft_original_endpoint_event_segment` in dftOrdinaryEventTrace:257.

Before a general positional diamond is authorized, a new boundary must bridge
these value-edited non-call endpoints to positional contexts/functions,
retain a coherent unmatched-event annotation across mixed aborts, and supply
whatever observation directions the final consumer actually needs. Count
balance must be proved, not inferred from equality of event sets (which ignores
multiplicity). Reverse ordinary call readiness needs the residual exclusion,
labels and phase above discharged. No additional hypotheses may be added to
the frozen target to bypass these obligations.

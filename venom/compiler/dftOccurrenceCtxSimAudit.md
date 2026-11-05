# Fixed-oracle occurrence-to-ctx_sim assembly audit

Scope: C3.7.3. This is a signature audit, not an all-edge correctness theorem.
Frozen statements and protected definitions are unchanged.

## Checked common interfaces

* `dftOrbitObservationScript.sml` supplies `dft_orbit_observation w C D c d`, reflexivity and transitivity. The fixed address oracle and initial configurations are outside all terminal/memory quantifiers. Terminal-forward transport forgets administrative counts, preserves the result exactly except for Abort state, and thus preserves Halt state. Memory-backward transport covers every nonempty range observation, including divergent trajectories, with equal memory and equal ranges. It permits a different instruction (needed for flips). It does not require event/counter equality or intermediate numeric realizations.
* `dftAllocationRootsScript.sml` derives lookup-local `dft_ctx_ids` for both sides of `dft_fn_rel` and of `dft_original_context`. `dft_fn_rel_entry_roots` transports the first-match entry lookup and proves validity of both occurrence starts. Entry names have type string option; NONE is a separate branch. `dft_context_entry_valid` applies equally to intermediate original contexts. Entry block labels still need structural transport at integration.
* `dftOccurrenceAllocation`: `dft_two_root_oracles_exist` provides ONE address oracle, a finite source list and uniform numeric compatibility for valid roots. Whole-orbit uniqueness and finite support were checked in E0348-E0350. Unmatched-event provenance is NOT a remaining allocation requirement. This does not itself prove semantic transport.
* `dft_occ_terminal_transport_ctx_sim` is the checked conditional native terminal consumer. `dft_shaped_context_external_terminal` supplies the source Halt/Abort classification from shape, without restricting callees. `dft_raw_occ_adequacy` and `dft_occ_observation_raw` are the native/raw observation boundaries. ctx_sim permits existential target fuel; no same-fuel optimization is needed.

## Exact normalized path to cover

`dft_ctx_normalized_path` (dftNormalizedEndpointScript.sml:110-119) yields an intermediate M and an RTC from C to M. Each edge is

    dft_original_context C A /\
    dft_pos_context_edge (dft_pos_provenance_guard C M) A B /\
    dft_original_context C B.

There is only one syntactic swap constructor, not an opcode-indexed datatype.
`dft_normalized_provenance_edge` (same source:172-187) exposes fi, bi, pre, x, y, post; B is exactly `dft_pos_edit_ctx ... A`, the selected block in A contains pre++[x;y]++post, both instructions are nonpseudo/nonterminators, `~dft_must_order x y`, and `abort_compatible x.inst_opcode y.inst_opcode`. Fallible order comes from C-to-M, not an extra assumption. After the RTC there is a LIST_REL of block labels and `flip_rel` instruction lists from M to C'. The endpoint relation contains no semantic theorem by itself.

## Exhaustive opcode partition for one adjacent edge

Partition each opcode into GAS, INVOKE, or O (neither). The nine ordered cases below exhaust swaps; absence of an adapter is explicitly recorded, not inferred from another case. ALLOCA is excluded by original function provenance. Pseudos and terminators cannot be either swapped instruction. Malformed output lists, output collisions and undefined operands still require runtime/provenance discharge, even for the GAS cases.

| x / y | Existing exact interface | Missing boundary |
|---|---|---|
| GAS / GAS | `dftRootedGasOrbit$dft_pos_gas_root_orbit_segments`, both `dft_gas_orbit_observation_*` adapters | Derive runtime_ready, singleton outputs and distinct outputs from normalized provenance; supply positional root functions. |
| GAS / O | `dft_pos_rooted_mixed_orbit_segments` (dftRootedMixedOrbit:85-103), both `dft_mixed_orbit_observation_*` | Discharge nonuse/nonclobber, shape/label/inst_wf/no-ALLOCA and target rooted trajectory premises. Root relation at index zero comes from gas phase root. |
| O / GAS | Same mixed observation adapters can reverse a proven GAS/O orbit | Must first express the inverse positional edit and derive its readiness/noninterference from the original edge. `~dft_must_order x y` is directional; do not assume it for y,x. |
| GAS / INVOKE | `dft_pending_bounded_closed_retired` (dftPositionalPendingClosure:1607-1619), `dft_pending_cofinal_segments_retired`, `dft_pending_orbit_terminal_forward/backward`, `dft_pending_orbit_observe_forward/backward` | Package the same A,B,Z,ledger into the observation contract and initialize the aligned pending phase at roots. All these projections are conditional, not a direct root adapter. |
| INVOKE / GAS | Reverse the pending observation only AFTER constructing the inverse GAS/INVOKE orbit | Same inverse edit/readiness gap as O/GAS. Do not discard divergent-callee pending reads; finite allocation already handles them. |
| O / INVOKE | `dft_pos_rooted_orbit_segments` (dftPositionalRootedOrbit:22-33), observe_forward/backward at :85/:109 | Rooted phase initialization and readiness; count-free terminal-forward/backward projection from phase/cuts has not been packaged in dftOrbitObservation. Conditions exclude GAS, ALLOCA and INVOKE on O. |
| INVOKE / O | Could reverse the O/INVOKE observation | Inverse edit and rooted readiness must be proved; no direct adapter currently exported. |
| O / O | `dft_original_ordinary_root_transport` (dftOriginalOrbit:199-223) gives terminal-forward and memory-backward at fixed w | This edits by block VALUE (`dft_gas_edit_ctx`) rather than fi/bi position, and edits root function by value. Its environment excludes DELEGATECALL/CREATE/CREATE2 and requires label readiness and strict_dom_vars_defined. Need a positional adapter or a proved equality of edits plus discharge of all exclusions. No all-O coverage follows merely from the theorem name. |
| INVOKE / INVOKE | No semantic adapter needed IF impossible | Prove impossibility from `~dft_must_order` (conflicting INVOKE effects) or abort-order provenance. This exclusion has not been checked as a theorem by this audit. |

GAS/mixed adapters already have both terminal directions and both memory directions. Those directions do NOT by themselves establish the inverse-context root premises for a swap whose actual order is O/GAS or INVOKE/GAS. Root and context identity must match exactly.

## Final operand flips

`dft_flip_next` (dftFlipRuntime:141-146) is a one-step theorem for `dft_open_next a` under `dft_rel_interface`, `dft_rel_core`, and matching flip lists. It is not yet an occurrence-oracle theorem: the address-selection event, occurrence path/visit/saved metadata, fill/erase and iteration must be transported. `dft_flip_rel_ids` proves ID equality, useful for address alignment. `dft_flip_pure_tests`/`dft_flip_tests` and `flip_operands_step_inst_base` provide local computation. Missing outputs are (i) fixed-w occurrence step/iteration, (ii) terminal observation, (iii) memory observation with possibly flipped instruction and exact range equality, and (iv) construction of the context interface from the normalized endpoint relation. Memory cannot be omitted just because flipped instructions are pure: outside them the consumer must observe all memory instructions through the related frames.

## Required integration outputs (proposal, not new PLAN IDs)

1. Prove a shallow generic cofinal terminal/observation adapter for rooted ordinary-call and pending cuts, and root initializations using allocation roots. No new ledger equality in the public contract.
2. Derive an exhaustive normalized-edge classification with executable readiness witnesses: distinguish all nine cases above, prove INVOKE/INVOKE impossible, and resolve inverse orientations explicitly. Validate O/O positional compatibility and the special-effect exclusions before scheduling its full lift.
3. Supply positional O/O transport and occurrence-level flip transport with memory coverage. These are substantive missing interfaces, not routine rewrites of the current observation contract.
4. Once every case is checked, prove a single normalized-edge observation producer at fixed w and same initial erased state; compose by RTC using `dft_orbit_observation_trans` and positional function correspondence. Roots must be defined coherently across the finite path, not chosen separately for each observation.
5. Compose final flips, apply the one common-oracle allocation theorem ONLY at the two endpoints, and convert terminal/memory observations to native ctx_sim and raw memory coverage. Split missing entry/function/entry-label branches separately. Preserve ctx_eom_bounded using the actual fn'=dft_fn fn conjunct.

Disposition: the observation algebra, local GAS/mixed adapters, valid roots and finite allocation are checked. Full normalized-edge semantics, inverse orientations, O/O positional transport, flips, RTC root coherence and native memory assembly remain unproved. This audit requests a scoped C3.7 replan with low-risk probes for these interfaces; it does not close the C3.7 integration group or the frozen compiler theorem.

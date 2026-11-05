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

## Residual O/O audit after positional successful diamond (C3.7.14.3)

This section is diagnostic only. Build check on 2026-11-05 passed for
`dftPositionalOrdinaryCrossingTheory`, `dftPositionalOrdinaryBoundaryTheory`,
`dftGasProvenanceTheory`, and `o1ContractDftTheory`. It does not certify the
remaining compiler cheat.

Let c and d have actual cores `DftOpen (DftAt fn 0 bb s) stack n` and
`DftOpen (DftAt fn' 0 bb' s) stack' n'`, and four selected fetch equations
x,y on bb and y,x on bb'. These are paired actual cores, not independently
chosen value-level slots. Below pair means `dft_ordinary_swap_pair x y`.

| Case | Existing primitive boundary and exact extra premises | Missing positional/integration boundary |
|---|---|---|
| x succeeds, then y succeeds | Accepted `dftPositionalOrdinaryCrossing` selected successful diamond; `dft_occ_ordinary_observe_source_prefix` (OrdinaryObserve:264) takes pair, wf x/y, both actual cores, four fetches and the two OK equations. Returns observations after each first step, operand equality, ranges equality and conditional memory equality. | Package positive 2/2 segment with positional endpoint phase and both memory directions. The successful endpoint theorem alone is not this package. |
| x aborts immediately | `dft_ordinary_first_abort_crossing` (OrdinaryStop:246): pair, wf x/y, x not empty-output/effect-free, y operands defined at s, and x Abort. Returns y Abort of same code OR y OK followed by x Abort of same code. `dft_occ_ordinary_first_abort` (OccurrenceOrdinaryStop:64) additionally takes actual cores and three fetches and gives 1 versus 1..2 instruction steps. | Port terminal clearing with positional saved-frame relation; obtain 2 versus 2..3 steps, equal abort code (not abort state), stable stopped phase and observation package. Non-invisibility follows from forward ~must_order, not reversed ~must_order. |
| x OK, y aborts | `dft_ordinary_second_abort_crossing` (OrdinaryStop:265): pair and the OK/Abort equations, no totality or opcode-subset premise. `dft_occ_ordinary_second_abort` (:96) adds actual cores/three fetches and yields 2 versus 1 instruction steps, same abort code. | Positional clearing/stopped phase gives 3/2 segments. No equal abort-state claim is available or needed. |
| x Error, or x OK then y Error | `dft_ordinary_result_cases` (OrdinaryClosure:845) needs nonterminator AND independent no-Error premise. `dft_shaped_ordinary_outcome` (LocalOrdinaryClosure:7) supplies OK-or-Abort only with wf, no pseudo/terminator/INVOKE/GAS/ALLOCA, operand definedness AND exclusion of DELEGATECALL/CREATE/CREATE2. | Either establish a native/original admissibility boundary ruling out these Errors at the exact use site, or provide Error transport (and intermediate observation coverage). Static runtime readiness does not supply this. No such complete boundary was identified. |
| Halt or IntRet | `dft_ordinary_no_halt` uses nonterminator; `step_inst_base_intret_opcodes` plus nonterminator rules out IntRet, as in OrdinaryClosure:845-853. | Only routine use of pair's nonterminator clauses; does not rule out Error. |
| Outside selected slot, Enter/Done | Accepted positional unaffected-step and outside-memory boundaries (C3.7.14.1), generic in selected opcodes. | Compose with selected segment; do not rederive from global edit wrappers. |

### Intermediate observations, including stopping

All relevant memory primitives are context-independent and allow independent C,C':

* `dft_ordinary_observe_indexed` (OrdinaryObserve:180) requires pair and
  `step_inst_base y s = OK t`; for any idx it gives operand agreement for x,
  equal ranges, and equal memory if x has nonempty ranges. No special-opcode
  exclusion occurs. Symmetric pair plus this fact covers both successful
  intermediate directions. `dft_occ_ordinary_observe_prefixes` (:227) is the
  actual-core/four-fetch wrapper when both first successor cores are known.
* `dft_occ_ordinary_first_abort_observe` (OccurrenceOrdinaryStop:133) requires
  pair, wf x, forward ~must_order, actual cores/three fetches, x Abort,
  h<2, and a nonempty target observation. It matches that observation at
  source offset 0, with operand/ranges/memory equality. Partner y has empty
  ranges by `dft_ordinary_abort_crossing_ranges` (:117). Conversely source
  x at offset 0 needs a target x observation after y if y succeeds; if y
  aborts first, a separate argument must show the omitted x observation has
  empty ranges. The existing one-way cover does NOT prove this converse.
* `dft_occ_ordinary_second_abort_observe` (:170) needs pair, actual cores/
  three fetches and x OK. A nonempty target observation at offset 0 (y at s)
  is matched by source offset 1 (y after x), with full agreement. Converse
  coverage must additionally handle source x at offset 0, which is not
  visited by target when y aborts. This is another missing empty-range or
  matching boundary; do not infer it from equal abort codes.
* `dft_occ_abort_clear`, `dft_occ_abort_prefix_clear` and
  `dft_ordinary_abort_no_observe` separate terminal clearing from instruction
  execution. Cleared aborts have no further open observations. They do not
  remove pre-abort observations.

`dft_ordinary_sync_success_cover`, `...first_abort_cover`,
`...second_abort_cover` and their segment wrappers (OrdinaryClosure:642-843)
are only target-to-source `dft_ordinary_prefix_cover`. They impose global
`dft_gas_edit_fn`/`dft_gas_edit_ctx` identity and cannot be applied as indexed
positional relations in the presence of duplicate equal blocks/functions.
The primitive observe and stopping facts above avoid that identity problem.

### Special effects are a real residual, not a proved exclusion

`exec_delegatecall_def` (venomExecSemantics:509-522) and `exec_create_def`
(:528-546) inspect `extract_venom_result ... (run evm_s)`. SOME plus singleton
output yields OK; NONE yields Error ("non-terminating or invalid state").
Thus wf and defined operands alone do not syntactically establish totality.
DELEGATECALL, CREATE and CREATE2 remain allowed ordinary opcodes unless a
separate provenance/admissibility theorem excludes the specific situation.
No such exclusion follows from the pair definition or runtime_ready alone.
Their memory ranges ARE covered by `dft_ordinary_ranges_cong` (explicit
DELEGATECALL/CREATE/CREATE2 Resume cases at OrdinaryObserve:139-153), and
successful effects are covered by the opcode-generic observe primitives.
The first-Abort partner classification (OrdinaryStop:72) legitimately
excludes these opcodes only in the RETURNDATACOPY-partner branch; it is not
a global pair exclusion.

Required next design decision: supply exact admissibility/Error interface
and bidirectional pre-abort memory coverage (or revise the demanded
integration contract if only one direction is mathematically needed), then
port the small stopping/observation wrappers to common positional witnesses.
This audit establishes neither impossibility nor a counterexample.

## Special-effect Error coverage decision (C3.7.14.6 replacement diagnostic)

E0366 invalidated the blanket empty-partner-range proposal, not the frozen
task. `dftOrdinaryErrorTheory` now builds with just the checked classification
`dft_ordinary_error_special` (committed a49c680c2). No dftGuards import is
retained: its unrestricted empty-write helper still treats GAS as neutral.

### Actual Error and readiness interfaces

* `exec_delegatecall` and `exec_create` return Error on failed extraction, or
  on a non-singleton output list after successful extraction. The surrounding
  `step_inst_base` branches additionally reject malformed operands and
  undefined evaluations. wf and operand readiness eliminate those shape/
  evaluation branches, not the extraction branch.
* `extract_venom_result_def` (venomExecSemantics:456-488) returns NONE iff
  the run result is NONE, or SOME with a final context list not of length one.
  EVM exceptions with a singleton final context are NOT native Error: they
  are extracted as a failed call/create with output zero. Thus arbitrary
  EVM failure is not a counterexample. To rule out the residual native Error,
  prove run totality AND singleton final context for the constructed state.
* `make_venom_create_state_def` (:428-442) starts with one context, a Code
  return destination, account transfer, rollback and tx parameters from s.
  Whether its `run` always terminates retaining one context is a substantive
  external-semantics boundary, not decided by this audit. No divergent EVM
  instance has been checked.
* `dft_pos_ordinary_selected_success` (:64-74) assumes both OK results; it
  cannot supply Error-free execution to the exhaustive consumer. Other
  premises are positional edit/runtime readiness, two original contexts,
  pair, wf, phase, actual cores/slot/index. `dft_pos_phase_def` (:64-74)
  supplies original readiness on both sides. `dft_original_ready_def` and
  `dft_original_control_ready_def` (OriginalRuntime:9-32) reduce that to
  structural original-function/block facts, reachability, and an activation
  cut. `dft_original_cut_def` (ProtectedRuntime:16-18) is schedule plus
  activation-cut; its operand theorem supplies variable definedness. None
  of these definitions asserts EVM run totality or a final context shape.
* At the frozen compiler boundary `o1_run_state_ok` is initial-state-ok,
  fmp initialization and code-layout-valid. Initial-state-ok fixes vars,
  halted, memory and allocas/frontier (unitTransformDefs:96-100), not a
  special-effect result. `o1_ctx_shape` is ctx wf and per-function shape.
  No direct native-Error exclusion is present. A derived EVM boundary may
  nevertheless prove it, so absence of a hypothesis is NOT falsehood evidence.

### Observation comparison

`dft_open_observe_def` (OpenMachine:100-105) requires the actual current
instruction fetch. It does not allow observing an arbitrary instruction in
an earlier state. `dft_orbit_observation_def` (OrbitObservation:13-30)
allows a *different* source instruction, but requires equal memory AND
exactly equal range lists. The one-way ordinary prefix cover is stronger:
it requires the same instruction and operand agreement as well.

If x=CREATE errors before y=MLOAD, source can observe x at the selected
entry, then Error/Done tails have no observations. Target observes y at its
entry before attempting x. Matching target y by an unexecuted source y is
not licensed. Matching it by source x is allowed only if range lists happen
to agree; there is no generic equality. For example, a zero-size CREATE
init-code range is not generally the positive 32-byte MLOAD range. This is
an interface obstruction, not a checked concrete execution counterexample.

The original partner-range proof fails for a precise reason:
`write_effects CREATE = write_effects CREATE2 = all_effects DIFF
{Eff_MEMORY;Eff_IMMUTABLES}`. Both read all effects, so independent partners
have empty writes, but may read memory (MLOAD). DELEGATECALL writes memory,
so its independent partners cannot read memory; this does not generalize.
Replay of x Error after a successful y bounds the target suffix but leaves
the target's initial y observation uncovered.

### Smallest repair / probe boundary

The unresolved obligation belongs to C3.7.14's exhaustive observation lift,
not to the already proved successful diamond. Preferred repair candidate:
for wf, defined-operand CREATE/CREATE2 at original-ready reachable states,
prove `extract_venom_result ... (run (make_venom_create_state ...)) <> NONE`
(and the analogous delegatecall fact if needed), via an EVM termination/
final-context invariant. This supplies totality only where actually needed,
without altering protected definitions or adding hypotheses to frozen goals.
No such theorem was identified by this bounded audit.

If that boundary is not valid, a separately authorized probe should first
check the narrower proposed helper, not declare the whole task false:
choose disjoint-output CREATE with literal operands [0;0;0] (or another
concretely failing constructed EVM input), and literal-offset MLOAD whose
range differs from CREATE's; verify pair/wf and compute failed extraction.
Use a two-instruction selected suffix with no earlier matching ranges and
empty stack to test actual orbit memory coverage. Only if a failing EVM
instance is found should it be extended to original-ready provenance and
ultimately to the frozen compiler/mem_inv contract. Replacing Error by
Abort or assuming failed extraction without computation is not evidence.

Diagnostic conclusion: exact pre-Error memory coverage remains conditional
on an unproved EVM result-shape boundary. Neither semantic impossibility nor
native totality has been established. Do not authorize unrestricted Error
coverage merely from independent variable-update framing.

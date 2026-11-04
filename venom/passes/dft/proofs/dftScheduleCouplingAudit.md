# Single-edit coupling interface audit (C3.2.4)

This is a design audit, not a proved semantic simulation theorem. No assertion
below supplies an assumption to HOL. The combinatorial factorization is proved
in `dftScheduleEditsScript.sml`; semantic closure remains to be proved.

## Exact consumer contract and directions

* `o1PassContractScript.sml:239-244`: `ctx_sim D C C' s s'` is
  `!fuel. terminates (run_context fuel C s) ==> ?fuel'.
  dead_result_rel D (run_context fuel C s) (run_context fuel' C' s')`.
  Source termination, not target termination, is the antecedent. The witness
  `s` in the frozen DFT theorem is outside this universal quantifier.
* `dead_result_rel_def` (same file:119-134) accepts Halt/Halt with observable
  agreement outside dead bytes, and Abort/Abort provided source Revert implies
  target Revert. It rejects Error and IntRet pairs. Exact observable Halt
  agreement and compatible Abort kinds suffice for arbitrary D; DFT should
  compose these stronger D-independent relations, not use
  `dead_result_rel_trans`, whose premise is `dead_wf D` (absent here).
* `gas_variant_def` (254-257) permits changing only `vs_gas_readings`.
  Neither variables nor the call oracle/context fields may be chosen afresh.
* `o1_lowered_inv_def` (590-593) is `?eom. ctx_eom_bounded eom C /\
  mem_inv (lowered_mem_fact eom) C s`. `lowered_mem_fact` uses
  `w2n s.vs_initial_fmp`, not a newly chosen frame bound.
* `unitMemInvScript.sml:96-109` characterizes `mem_inv` by a resolvable entry
  AND a fact at every raw-reachable pre-instruction state. Hence the required
  observation direction is target to source. Source termination is irrelevant
  for this part. Entry resolution must be transported separately.
* `ctx_eom_bounded_def` (o1PassContract:571-574) depends on `fn_eom`.
  Its transport uses `fn' = dft_fn fn`, not merely execution simulation.

No same-fuel result theorem is required by these consumers. Native fuel errors
must not be turned into terminal events by erasure. The stronger same-fuel
finite-block theorem `dft_run_block_gas` is a separate frozen obligation; its
input reading list can depend on its fixed fuel and does not discharge the
uniform context witness.

## Existing proved boundaries (and their limits)

`dftOccurrenceReplayScript.sml` exposes:

* `dft_occ_oracle_next w C c`: consult w at the current dynamic address, not
  at the total GAS counter. Addresses are path ++ [(block visit, inst_id)].
* `dft_occ_prefix_replay` / `dft_occ_numeric_replay`: finite replay under
  eventwise compatibility with a numeric oracle. They do not prove
  compatibility or a cross-context relation.
* `dft_raw_occ_adequacy`: target raw reachability gives an occurrence prefix
  under label distinctness, a sparse numeric oracle, and compatibility for
  all prefix lengths. The observed native state is materialized by dropping
  the GAS count from the original reading list.
* `dft_occ_observation_raw`: the converse observation boundary with an explicit
  finite prefix compatibility premise. There is no equal-counter requirement.
* `dft_occ_budget_prefix_replay`: erasure only before any zero-budget entry.
* `dft_occ_native_result`: budgeted first-hit result boundary, modulo Error
  text, with a specified native fuel. It is not itself the fuel-free terminal
  decoration theorem; its use must also cite the existing fill/decorates and
  native/open adequacy facts.

`dftOccurrenceOpenCallScript.sml` proves GAS residual operand/setup agreement,
receipt framing, push, and conditional return restoration. Its caller cut is
only a variable-write cut (`dft_cut_pair [(v,g)] [] s t`). It does not represent
an unmatched arbitrary effectful instruction. In particular it cannot justify
a general residual-prefix invariant by treating every crossing as a GAS write.

`gas_pair_commute` (separately owned dftBlockSim:1191-1205) assumes BOTH target
steps return OK. It supplies a gas-variant source for that finite successful
pair. It has no open/divergent INVOKE or prefix-observation conclusion. Its
statement may be used; its proof is owned by another run.

The current `dftRunRelScript.sml:2717-2809` already contains a proof of
`dft_run_block_gas`, using head-bubble and prefix gas-variant interfaces. Do not
replace its frozen statement. Its theorem-specific build/check status is a
separate completion check; this audit does not claim a new proof of it.

## Proposed semantic boundary (UNPROVED, for strategist review)

For two well-shaped contexts differing in ONE ID-preserving adjacent inversion
at one static block (and later for one operand flip), fix an arbitrary address
oracle `w : (num # num) list -> bytes32` BEFORE any trajectory quantifiers.
Let L(j), R(k) be the occurrence-oracle iterates from paired context entries,
started with equal non-gas data. The proposed boundary has two conclusions:

1. For every finite source trajectory reaching a top-level Halt or Abort,
   there exists a finite target trajectory reaching a compatible terminal
   result (observable equality for Halt, Revert implication for Abort).
   Quantifiers: forall w, starts, j, source result; exists k, target result.
   GAS counters, numbers of small steps, and native fuels need not be equal.
2. For every finite target trajectory at a pre-instruction observation,
   either its memory range list is empty, or there exists a source trajectory
   at the corresponding original-ID instruction with the SAME range list and
   initial_fmp. Quantifiers: forall w, starts, k, target observation;
   exists j, source observation. A stronger prestate relation may be useful
   internally, but is not part of the minimal consumer conclusion.

The range equality here is `inst_mem_ranges instL sL =
inst_mem_ranges instR sR`. Full memory equality at every observation is not a
consumer requirement: `lowered_mem_ok` only tests this range list and the
initial_fmp. Proving universal raw-observation coverage even for zero-range
instructions would impose unnecessary stopping constraints. An early abort
can skip independent pure computations; their target memory fact is trivially
true. Any proposed stronger interface needs a separate validation.

The boundary must hold uniformly for all w, not only the oracle extracted from
the final target run. Otherwise intermediate-schedule composition would need
an unjustified fresh GAS witness. Occurrence paths use original instruction
IDs throughout; block visits and suspended caller paths need preservation.
Only after finite schedule composition should w be chosen from the complete
final target trajectory and realized by one finite source reading list.

## Phase and stopping-case table

| Phase | Required transition/observation argument | Missing versus established |
|---|---|---|
| Synchronized before edit | Same next instruction except edited callee context; same relevant operands/effects, aligned dynamic path/visit | Cross-context ordinary step and entry preservation missing |
| One side has executed first swapped instruction | Keep an explicit bounded edit phase; use the appropriate pair diamond, not a general variable-only receipt | Effectful pair phase and observation diamond missing |
| Both swapped instructions completed OK | Rejoin data state (mod index/gas ghosts), reset phase | Finite same-context commute facts exist; occurrence/cross-context lift missing |
| GAS/GAS skew | Both consult w by their own IDs; counter values may differ | Existing GAS receipts/replay; phase closure missing |
| GAS/INVOKE skew | Execute the pending GAS on the required side, align invocation address and args; save caller phase on paired stacks | Local GAS operand/setup/push algebra exists; paired stack invariant missing |
| Inside callee, possibly forever | Couple callee prefixes with saved caller phase untouched; transfer observations without a return premise | Global recursive-context closure missing |
| IntRet delivery | Bind outputs and restore saved phase, then complete pending local edit | Conditional local restoration exists; trajectory invariant missing |
| Halt/Abort inside call | Deliver/propagate terminal result without demanding IntRet; forget dead pending variable receipts as justified by result relation | Terminal classification and propagation missing |
| First step stops early | Source-termination direction requires compatible target stop; target memory observation coverage needs a distinct no-skipped-memory argument | Successful pair diamonds do not cover this |
| Structural Error / fuel exhaustion | Exclude via readiness only where justified; otherwise Error need not satisfy ctx_sim's antecedent | Readiness at every intermediate cut and nonexhaustion use missing |
| Terminator / next block | Terminator remains last, same branch operands, increment visit on both sides | Static endpoint property exists; dynamic phase boundary missing |
| PHI/pseudo prefix | Preserve entry predecessor and incoming values; edits remain in nonpseudo body | Need explicit entry/phi coupling, not arbitrary instruction swapping |
| Operand flip | Same ID/opcode, range behavior and step result preserved under the legal flip | Operational normalization exists; occurrence observation lift missing |

## Adversarial checks and concrete missing interfaces

1. **Abort before a moved memory observation.** `abort_compatible` alone
   is NOT an observation theorem. NoFail memory operations can pair with a
   stopping instruction. Need a classification proof combining actual
   `dft_must_order`, effects, readiness, and abort behavior: an allowed
   crossing cannot hide a target nonempty-range observation behind a source
   stop. Validate all classes: ASSERT/ASSERT_UNREACHABLE/INVALID have no-output
   root barriers; RETURNDATACOPY writes MEMORY; INVOKE has callee effects.
   For example, an apparent RETURNDATACOPY/ILOAD loophole is excluded by
   `read_effects ILOAD = {Eff_IMMUTABLES; Eff_MEMORY}` and COPY's MEMORY write
   (venomEffects:59,126). This check is source-grounded, not a proved general
   classification. The all-opcode lemma is still missing.
2. **Effectful independence.** A variable-only cut is too small. A finite
   single-edit phase can retain the actual one-step pre/post states and a
   diamond certificate. It need not model an arbitrary residual list of
   noncommuting effects. Memory-range transfer requires operand agreement;
   exact global state equality at skewed cuts is not justified.
3. **Cross-context calls.** Same-context finite commute does not simulate a
   callee whose body is itself rescheduled. Single-edit context closure must
   be recursive, handling arbitrary re-entry into the edited block, and
   store a phase per active invocation rather than one global phase.
4. **Intermediate readiness.** `inv_edit_factor` only supplies order
   provenance. Each intermediate schedule must retain pseudos/terminator,
   ID distinctness, wf/SSA availability, legal operands, and the protected
   ordering needed by semantic lemmas. Do not assume an arbitrary
   intermediate is literally `dft_fn fn`. A generic ID-schedule well-formedness
   interface or a preservation theorem is needed before composition.
5. **Memory consumers.** Prove a boundary transferring `lowered_mem_fact`
   from equal ranges and initial_fmp, then use raw-reachable coverage and
   entry preservation. The existing `mem_inv_transport` uses the SAME initial
   state on both contexts; its statement cannot directly take s != s'.
   The characterization `mem_inv_raw_reachable` can be used directly, or a
   different-initial-states transport helper can be proved without changing
   the existing exported theorem.
6. **Native result consumer.** Prove the source terminating native result
   gives a nonexhausting finite source occurrence terminal prefix. Transport
   it in direction (1), decorate the finite target prefix with sufficient
   budget, and apply native adequacy. Keep Error-string quotienting separate
   from Halt/Abort, and do not conclude a fixed native fuel from erasure.
7. **Composition and one list.** Compose stronger D-independent result and
   range-observation relations under a fixed w over the finite edit chain.
   Then prove sparse finite-support realization using occurrence uniqueness.
   Individual per-fuel block gas witnesses cannot be substituted here.

## Suggested next proof boundaries (not an executor-owned PLAN)

The strategist should first authorize bounded probes/classification for (1)
and the intermediate well-formedness interface in (4), and decide an explicit
single-edit phase datatype/invariant with paired saved phases. Then separate:
ordinary/flip steps and range transport; successful pair diamonds; stopping
and nonempty-range exclusion; GAS/open-call/return transitions; finite-prefix
closure and terminal/observation projections; fixed-w finite schedule
composition; native consumer and finite-list realization. The semantic closure
leaves are not yet de-risked by this audit. No global simulation has been
inferred from local receipts or successful finite commutation.

## Protected-edge consumer map (C3.2.8)

`inv_edit_schedule_edges` and `inv_edit_rtc_schedule_edges` now prove that an
edge relation preserved by the final destination remains preserved after each
original-direction inversion, provided the destination IDs are distinct.
`inv_edit_rtc_perm` and `inv_edit_rtc_distinct` give the static projections.
These are checked list facts, not dynamic readiness facts.

To apply them to an instruction list, recover the original instruction at
each unique ID and instantiate the protected relation with the relevant
union of:

* original within-block def-to-use edges (`dft_must_order`'s first disjunct);
* original read/write-effect conflicts and no-output empty-effect root edges;
* edges from original instructions to the original terminator;
* original incompatible-failure edges supplied by `dft_fallible_order_kept`.

The final DFT block relation supplies the first three; the fallible-order
premise supplies the fourth. Pseudo instructions should be kept as a fixed
prefix, not placed into the body inversion chain. Endpoint distinctness and
PERM provide ID membership and static identity, but instruction reconstruction
and legal operand flips are still separate interfaces.

What this does NOT establish: availability of strict-dominator variables at a
particular runtime state, availability of same-block variables after prior
steps, labels in FDOM, correct PHI entry operands, valid external request
state, or absence of native fuel exhaustion. Reverse def/use and def/def
independence of a crossed pair still require source SSA and unique definitions;
they do not follow by silently extending `dft_must_order`. Such static bridges
and dynamic preservation lemmas remain separate semantic obligations.

## Checked stopping-crossing audit (C3.2.7.2)

`dftStoppingRangesTheory` now checks the following boundaries (no oracle
assumptions). Here `~dft_must_order x y` is directional: x originally
precedes y and the edit is allowed to move y before x.

* `dft_no_memory_effect_ranges`: absence of MEMORY in both opcode effect
  sets implies `inst_mem_ranges i s = []`, for every state s.
* `dft_memory_writer_crossing_ranges` and
  `dft_memory_writer_crossing_not_invoke`: if x writes MEMORY and the
  directional edge is absent, y has empty direct ranges in every state and
  is not INVOKE. Thus direct range emptiness is not silently used to cover
  observations in a skipped callee.
* `dft_nonroot_abort_crossing_ranges` / `dft_abort_crossing_not_invoke`:
  for wf nonterminating-opcode x, an actual Abort and absent directional
  edge imply the same two conclusions about y. The edge's absence excludes
  root barriers; the existing checked `dft_swap_nonroot_abort_class` then
  leaves only INVOKE or RETURNDATACOPY (the latter ExHalt). Both write MEMORY.
* `dft_nonterminator_halt_crossing_ranges` /
  `dft_halt_crossing_not_invoke`: for nonterminating-opcode x, an actual Halt
  and absent edge likewise exclude direct ranges and calls in y. Existing
  `step_inst_halt_opcodes` reduces this case to INVOKE.
* `dft_invoke_crossing_ranges`: the INVOKE version does not require any
  return/stop premise, so also applies to an open or divergent call.

These statements concern the *crossed* instruction y, not x: a stopping
INVOKE can have observations in its callee and a RETURNDATACOPY can have its
own direct ranges. Such observations still require matched-prefix transport.
They also do not say that a target trajectory after successful y and a later
x can be matched after a source stop at x: compatible terminal behavior and
unreachable-success exclusions require the future phase proof. Structural
Error, missing readiness, IntRet/block transitions, arbitrary finite-prefix
closure, and recursion through paired stacks remain separate obligations.
No counterexample to the frozen task theorem is claimed by this audit.

Verification: `holbuild(targets=['dftStoppingRangesTheory'])`, including its
repaired SCCP prerequisite, succeeds. The new theory has no cheats.

## Bounded square checkpoint (C3.2.9)

`dftOccurrenceSquareTheory` defines a six-configuration certificate with four
actual `dft_occ_oracle_next` equalities. Phase tags select before/middle/after
on each trajectory independently. Left/right prefix projections and the
final join projection are checked. The join forgets function and block
identity but requires the same state, empty-budget At control, stack, counter,
and occurrence ghosts; it is not a recursive caller relation.

`dft_gas_square_ok` constructs the certificate by computing two distinct-output
GAS instructions in opposite order. It assumes no endpoint equality, numeric
oracle agreement, or transition certificate. The shared address oracle w is
arbitrary and can give different values at the two original IDs; both runs
consult the same address for each ID. Distinct finite-map updates commute,
indices reach 2 and counters increase twice. `dft_gas_square_inhabited`
instantiates IDs 0 and 1 from an arbitrary instruction template, so these
premises are non-vacuous. The two directional absent-edge theorems are also
checked from the actual GAS effects/uses and nonempty output lists.

Limits: this certificate does not assert that middle states agree, establish
any general pair diamond, or transport observations at its skewed cuts. The
GAS test has empty stacks and two-instruction blocks which need not terminate.
Saved caller phase relations, recursive entry/return, terminal propagation,
readiness of intermediate schedules, and native adequacy integration remain
unproved; no global uniform-witness theorem follows from this checkpoint.

## Recursive GAS/GAS syntax interface (C3.2.10)

`dftOccurrenceGasEdit` now defines a fixed adjacent replacement through blocks,
functions, contexts, controls, and all saved caller frames. Only syntax fields
are mapped; state, counters, results and occurrence ghosts are retained. The
cut relation has a synchronized case excluding the edited middle index, and a
middle case generated by actual next transitions from a common before-cut.
Safety requires zero budgets and actual INVOKE slots in saved callers; it does
not contain a simulation/trajectory assumption.

Checked interfaces: function/block lookup, entry label and setup_callee,
PHI evaluation and prefix length, entry-index bound, instruction lookup outside
the pair, pair lookup, saved INVOKE-slot preservation, stack safety mapping,
push/pop structure and return-index exclusion. Empty-stack initialization and
a genuine Enter-to-before-to-middle instance are checked. No recursive
transition preservation or trajectory transport is claimed here. Those remain
C3.2.11 and C3.2.12, and unrestricted GAS/INVOKE and effectful closure remain
separate unresolved work.

## Actual GAS/GAS transition closure (C3.2.11)

`dft_gas_edit_rel_next` proves preservation by the actual occurrence-oracle
next function under the stated adjacent well-shaped distinct-output GAS edit.
The generated middle phase rejoins after the two GAS steps with arbitrary
mapped stacks; the synchronized phase uses unchanged-fetch commutation through
entry, shared base-instruction results, INVOKE pushes/errors, and all return
results. Source safety and exclusion of the middle index are preserved using
actual saved INVOKE slots and the PHI-entry bound. No callee termination or
simulation hypothesis occurs in these proofs. This is recursive one-step
closure for this single fixed GAS/GAS edit only; trajectory/observation
corollaries and the general effectful/GAS-INVOKE extension remain distinct.

## Recursive GAS/GAS trajectory checkpoint (C3.2.12)

`dftOccurrenceGasEditTraceTheory` now checks:
- `dft_gas_edit_rel_iterate`: arbitrary finite FUNPOW prefixes preserve the
  relation under a fixed address oracle, with no call-depth bound.
- `dft_gas_edit_rel_terminal`: related configurations have exactly the same
  empty-stack Done result and occurrence count, in both directions.
- `dft_gas_edit_rel_observe`: every target nonempty direct-range observation
  has a source observation with the **identical instruction and state**
  (only function syntax may differ).
- `dft_gas_edit_init_iterate` and `dft_gas_edit_containing_init`: initial
  trajectories are related; the latter explicitly includes bb0 in the initial
  function and that function in the context, leaving other blocks/callees free.

These conclusions compose directly: apply init_iterate at j, then
rel_terminal or rel_observe. The proof excludes generated middle phases using
`dft_gas_edit_middle_active`, whose fetched instructions are GAS, and treats
synchronized observations using the checked outside-pair fetch boundary.
Quantifying over each finite prefix includes observations during divergent
recursive runs and does not require successful returns.

Restriction: one fixed adjacent GAS/GAS replacement with singleton distinct
outputs, no operands, and distinct instruction IDs. This does NOT establish
effectful adjacent edits, GAS/INVOKE saved residual phases, intermediate
schedule readiness, full DFT composition, finite gas-list realization,
`dft_run_block_gas`, or `dft_ctx_sim_gas`.

## Shared non-PHI synchronized transition kernel (C3.2.13)

`dft_nonphi_edit_phis_list`, `dft_nonphi_edit_phi_length_list` and their
block-edit corollaries check entry preservation for any adjacent non-PHI
pair. `dft_nonphi_edit_open_entry`, `dft_nonphi_edit_open_next`,
`dft_nonphi_edit_next_inf` and `dft_nonphi_edit_occ_next` check actual
transition equalities, using the existing structural maps. The At boundary
`dft_gas_edit_open_at` was already opcode-independent and is reused unchanged.
The occurrence theorem permits arbitrary oracle and suspended callers; its
hypothesis is equality of the current fetched instruction, not simulation,
termination, or an endpoint. `dft_nonphi_edit_occ_next_outside` discharges that
fetch hypothesis by excluding the edited positions. GAS/GAS exported entry,
open-next, next-inf and occurrence-next statements remain unchanged as wrappers.

This kernel deliberately does not transport readiness of saved frames for
edits containing INVOKE and does not cross the swapped pair. GAS/INVOKE
residual phases, general independent diamonds and full scheduling composition
remain open, as do both frozen task obligations.

## Same-context suspended GAS/INVOKE transport

`dftOccurrenceSuspendedTheory` now supplies an actual-transition boundary
for one distinguished caller pair with a pending GAS. `dft_suspended`
keeps arbitrary fixed caller/ghost tails and an identical, arbitrarily deep
nested prefix; the active control and address agree, but counters need not.
`dft_suspended_next` covers Enter, At (including nested INVOKE and GAS), and
Done (including nested pops, distinguished return, and stack-clearing
failures). `dft_suspended_prefix_observations` transports every finite
prefix up to a first distinguished exit, including identical active
instruction/state observations. It assumes neither callee termination nor
a common endpoint, and makes no assertion after that exit.

`dft_suspend_crossing_entry` constructs this relation from two actual
GAS-first steps versus one actual call-first step on adjacent reordered
caller blocks. `dft_suspend_call_failure` separately synchronizes malformed,
missing, undefined-argument, and empty-callee setup failures; successful
setup is not a global simulation premise. `dft_suspend_return_discharge`
performs the pending GAS after successful restoration and proves equal
caller states at the exact common next index. These boundaries require
zero erased budgets and preserve independently specified tails. Where an
empty stack is used before/after the crossing, its saved occurrence stack
must also be empty (the machine clears stale saved ghosts on such steps).

This remains **same-context** callee transport only. Recursively edited
callee contexts, general independent effectful edits, intermediate schedule
readiness, schedule composition, and the frozen context/block obligations
are not established by this theory.

## Mixed GAS/INVOKE caller boundary (C3.2.15)

`dftOccurrenceCallStackScript.sml` now provides a mixed stack, rather than
one distinguished residual under an identical nested prefix. Each paired
caller retains its own common saved path/visit. A normal caller has mapped
syntax and equal saved states at an actual INVOKE slot on both sides. A
pending caller has the single-variable GAS cut, source index `SUC (LENGTH
pre)`, target index `LENGTH pre`, and its value fixed by the saved address.
Counters are independent. Empty/cons/head-inversion, alignment lengths and
erased-frame boundaries are exported.

The checked transition boundaries are:

* `dft_mixed_init` and `dft_mixed_sync_enter`: mapped entry, including missing
  block and PHI failure, with the remaining mixed callers unchanged unless
  the machine clears them.
* `dft_mixed_sync_at`: actual oracle steps outside both edited slots.
  INVOKE lookup/setup uses the mapped context and enters a mapped callee;
  it pushes an ordinary frame onto any mixed tail. Setup failure clears
  the stacks. GAS and ordinary instructions have their actual transitions.
* `dft_mixed_sync_done`: an ordinary pop rejoins synchronization; a pending
  pop produces `dft_mixed_discharge`, not synchronization; a failed return
  or non-return result clears the stacks. No callee termination premise is
  used: this theorem classifies the actual Done constructor when present.
* `dft_mixed_discharge_next`: one actual target GAS step rejoins with the
  source while retaining the remaining mixed stack and its saved addresses.

`dft_mixed_pending_instance` and `dft_mixed_two_pending_instance` give symbolic
non-vacuous saved frames at the actual two call indices.
`dft_mixed_two_pending_pop` and `dft_mixed_two_pending_discharge` expose the
unchanged outer descriptor/address in the actual transition equations.
`dft_mixed_two_pending_return_discharge` additionally requires both frames
to be pending and composes the actual inner return and target GAS discharge.
It permits return arity failure explicitly rather than assuming success.

This is a boundary checkpoint only. It excludes active execution across the
edited pair and does not prove unrestricted recursive trajectories,
intermediate-phase observation transport, schedule readiness, whole-schedule
composition, terminal step accounting, or realization by a finite gas list.
The frozen block and context obligations remain unresolved.

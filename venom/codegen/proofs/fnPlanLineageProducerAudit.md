# Native producer closure audit

Scope: `C3.bridge.2.closure_audit`, 2026-11-07. This is an interface audit,
not a proof of a global invariant or of `lineage_state_block_plan`. No SML
statement, frozen relation, or definition is changed by this document.

## Notation and authority

The following are **document abbreviations only**, not new HOL predicates:

- `I(s,v)` = `MEM (Var v) s.ps_stack \/ Var v IN FDOM s.ps_spilled`.
- `R(s,v)` = `LIST_ELEM_COUNT (Var v) s.ps_stack +
  (if Var v IN FDOM s.ps_spilled then 1 else 0)`.
- `L(bb,i)` = `live_vars_at (liveness_analyze fn) bb.bb_label i`.
- `O(V,v)` = `?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  MEM v di.inst_outputs /\ MEM db.bb_label V`.
- `Opre(V,bb,i,v)` = `O(V,v) \/
  ?di. MEM di (TAKE i bb.bb_instructions) /\ MEM v di.inst_outputs`.
- `P(s,V)` = `!v. I(s,v) ==> O(V,v)`.
- `B(bb,i,s)` is the existing `native_live_boundary fn bb i s`:
  live coverage and live unit budget, not exact inventory.
- `Ex(prefix,names)` = `EVERY (\v. ~MEM (Var v) prefix) names`.
- `init` abbreviates `init_cleanup_plan_state ch growth spill_base lbl_ctr`.

Candidate schemas below expand these abbreviations before formalization.
They are missing obligations to review, **not asserted true theorems**.
No schema authorizes an implementation or strengthens the frozen theorem.

## Producer-consumer matrix

| Required row | Exact checked consumer / premise | Existing producer and limits | Missing producer / induction index |
|---|---|---|---|
| Initial chronological support | `native_chronological_prefix`, lines 60-64: `!v. I(ps,v) ==> Opre(visited,bb,n,v)`, and `B(bb,n,ps)` | `initialized_entry_boundary_resources` gives prefix origins and B for the HD block after `prepare_params_plan`, at `n = LENGTH (get_params bb.bb_instructions)`, from readiness and nonempty blocks. `ready_entry_static_boundary` gives no entry predecessors/PHIs and reachability. | No missing entry parameter origin lemma. Missing whole-trace origin transport is schema T below; `native_chronological_prefix` alone excludes PHI/JMP/parameter positions. Index: mutual successful DFS trace, then original instruction position. |
| Initial live coverage / unit budget | `native_chronological_prefix` requires B; `generate_phi_plan_live_budget` requires coverage and `R <= 1` for live names other than its output | `initialized_entry_boundary_resources` initializes both live facts after parameter preparation. `native_inst_prefix_resources` propagates the entry-specific contract through non-JMP/non-PHI instructions; `initialized_entry_jmp_preterminal` packages the entry JMP case. | Arbitrary native DFS incoming B is missing. It cannot be replaced by the entry-only prefix-origin predicate. Schema N identifies the desired native boundary; initialization, unique edges and PHI/JMP transfer must supply it without runtime replay. |
| Block entry cleaning | `analyzed_single_pred_cleanup_resource` exactly preserves `R(s,v)` for `v IN L(bb,0)` under readiness, lookup and predecessor count 1 | That theorem is transport, not initialization. Cleanup spill equality and input count facts are in Inventory. Entry initialization already accounts for the actual entry setup in `initialized_entry_jmp_preterminal`. At joins the successful-JMP suffix and empty spills are available from Edge. | For unique predecessors, supply incoming coverage/count and liveness edge transport before applying cleanup; schema U. Join setup must connect the actual clean/parameter worker state to the PHI schedule state; PHI schedule replay alone is not a theorem about full `generate_block_plan`. |
| PHI physical selection | `generate_phi_plan_live_budget`: `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist`. `generate_phi_plan_observation_frame`: same SOME depth on both states, bounds, equal alloc, equal selected-live test, conditional post-write output-depth equality | `lineage_dfs_join_phi_schedule_ready`, `lineage_dfs_join_phi_state_replay`, and `lineage_dfs_join_phi_common_suffix_actual` already supply actual paired PHI replay through native predecessor cells. EntryWitness's `reachable_phi_live_entry_representative` is static demand information, not a physical depth equation. | For compile-time resource accounting, selection must be threaded at each PHI schedule index with coverage/count of remaining incoming values. For runtime replay do not demand a second global selection proof: use the existing paired schedule endpoint. |
| PHI output freshness | `generate_phi_plan_live_budget`: singleton `inst.inst_outputs = [out]`, `~MEM (Var out) ps.ps_stack`, `Var out NOTIN FDOM ps.ps_spilled`; it returns live coverage/count only | Ready `inst_wf` supplies PHI singleton shape. `chronological_origin_output_fresh` supplies absence from origin support with current block unvisited and earlier current positions only. `generate_phi_plan_inventory_origins` transports origins without freshness. | Native PHI freshness can follow T plus a PHI-prefix origin contract, not from SOME-ness. Runtime revisit freshness is **not** a premise of `lineage_dfs_join_phi_common_suffix_actual`. Do not build it merely to consume that endpoint. |
| Terminal edge live transfer | `generate_inst_plan_jmp_live_terminal`: JMP, empty outputs, actual successful plan, `join_target_ops = SOME targets`, `set (MAP Var next) SUBSET set targets`, live input `R <= 1` | `analyzed_live_out_jmp` gives analyzed live-out/input-target equality at reachable terminal JMP. Edge gives successful join suffix and empty spilled map. `entry_jmp_live_terminal` consumes preterminal entry resources; `initialized_entry_jmp_residual_zero` closes the first-entry JMP residual-live case. | For other native predecessor blocks, preterminal unit budget remains missing (N). Unique nonjoin edges require liveness propagation, not join-target reasoning. Successful suffix equality alone neither bounds multiplicities nor removes the residual prefix. |
| Join residual shielding | `ordinary_interval_shared_core_replay`: `Ex(prefixP,L(bb,a))`, `Ex(prefixQ,L(bb,a))`, and both prefixes exclude outputs at every `a <= k <= j`; operand availability in common base, operand bound <=16, non-JMP | EntryProduction's JMP residual-zero removes **live** names given a unit budget; it is conditional for arbitrary blocks. ReturnCut's `ordinary_output_post_phi_demand_exclusion` excludes an output from demand at a cut, not from the physical residual. Actual PHI common-suffix theorem gives live membership in suffix, not exclusion from prefixes. | Schema S below is the critical absent physical producer. It must establish live exclusion **and future ordinary-output exclusion** on both sides, or a strictly weaker actual-query observation producer. No inference from `I(s,v)` or suffix coverage is valid here. |
| Runtime revisit observation replay | `generate_phi_plan_observation_frame` and ordinary shared-core replay, eventually block op equality plus allocator equality | Frozen `lineage_state_step` already includes successful replay of the predecessor's DFS ops. `lineage_state_actual_dfs_alloc` and `lineage_state_actual_dfs_label_counter` align fields using successful function planning. Paired actual PHI endpoint covers revisits subject to its stated join/PHI hypotheses. | Schema S (or a query-specific replacement) plus cleanup/full-worker integration and unique-predecessor edge replay remain missing. Index: `lineage_state_ind` for edge history, inner native worker prefix for observations. No `~MEM lbl visited` at runtime. |

## Exact proposed producer schemas and dependencies

### T. Compile-time chronological contract (missing global theorem)

Proposed simultaneous successful-trace contract:

```
plan_aux_trace lv dfg cfg fn wl V ps (ops,V',out) events /\
lv = liveness_analyze fn /\ codegen_ready_fn fn /\ P(ps,V)
  ==> P(out,V')

plan_succs_trace lv dfg cfg fn saved spilled wl V ps (ops,V',out) events /\
lv = liveness_analyze fn /\ codegen_ready_fn fn /\ P(ps,V) /\
(!v. MEM (Var v) saved \/ Var v IN FDOM spilled ==> O(V,v))
  ==> P(out,V')
```

The needed *internal* contract at each present fresh AUX head additionally
records `P(ps,V)` for that head's own pre-event V, not merely final V'.
`events` store `(label,state)`, not V. Do not state event freshness using
only final V': the current label is then included. Use induction-local
heads or an explicitly indexed trace certificate, to be designed later.

Mutual index: `plan_aux_trace_ind`. The fresh block contract is
`P(ps,V) /\ ~MEM bb.bb_label V /\ actual block plan ==> P(out,bb.bb_label::V)`.
It requires native operand coverage to invoke ordinary-origin transport
and terminal target coverage to invoke JMP inventory transport. Thus T
cannot be proved by origin preservation alone without the resource half N.
Missing lookups add a visited label but no variables. Visited heads do not
execute a block. The successor cons resets stack/spills from the saved
pair; its sibling retains the previous current inventory, changing allocator
and label fields only. Both SUCCS support premises are necessary.

`plan_trace_key_invariant` already proves visited monotonicity internally;
public inclusion/exclusion/distinct-key corollaries are in CallTrace. Trace
completeness/erasure and `dfs_block_state_trace_event` connect actual calls
to successful traces. These are chronology certificates, not resources.

### N. Native boundary certificate (missing; requires design review)

Desired scope is **first compilation only**. With actual analyzed successful
function planning and a fresh DFS AUX head for `lookup_block lbl = SOME bb`,
let `s` be the actual worker state after cleanup and parameter preparation,
and `n = LENGTH (get_params bb.bb_instructions)`. Candidate conclusion:

```
(!v. I(s,v) ==> Opre(V,bb,n,v)) /\ B(bb,n,s)
```

At every actual `native_inst_prefix ... n len xs s k qs`, desired result:

```
(!v. I(qs,v) ==> Opre(V,bb,n+k,v)) /\ B(bb,n+k,qs)
```

Here `xs = non_param_insts bb`, `len = LENGTH bb.bb_instructions`, and V is
that block's fresh pre-call visited set. Unlike `native_chronological_prefix`,
this desired worker certificate must include PHIs and terminal JMP; it is
not an existing theorem. Parameters and cleanup precede `s`, not an arbitrary
state supplied by the caller. Acyclic proposal: simultaneous origin/resource
induction on successful DFS evaluation with an inner worker induction.
Resources are independent of T's freshness conclusion except where SSA
converts origin support to fresh current output. No lineage replay theorem
may be used as an incoming native-resource producer.

### U. Unique-predecessor edge initialization (missing packaging)

For a ready analyzed reachable edge pred -> lbl with exactly one CFG
predecessor, actual successful predecessor block output `after`, candidate
edge result before cleaning is:

```
(!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==> I(after,v)) /\
(!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==> R(after,v) <= 1)
```

This must follow from native preterminal/terminal resources and analyzed
edge demand, not from `generate_block_plan = SOME` alone. For exactly one
predecessor readiness rules out collected PHIs; the existing single-pred
cleanup count theorem then transports these bounds. Parameter preparation
on a nonentry block must be justified by readiness rather than assumed an
identity. Runtime unique-edge replay additionally needs a relation to the
compiled incoming state, not merely these two resource facts.

### S. Physical ordinary-region shielding (missing semantic bridge)

At a multi-predecessor block with PHIs under *exactly* the hypotheses of
`lineage_dfs_join_phi_common_suffix_actual`, take
`a = LENGTH (collect_phis sb.bb_instructions)`. A sufficient candidate
strengthening of that endpoint is to choose its existential witnesses
`prefixL prefixD suffix ops al` so that, **in addition to its existing
schedule equations and suffix-live coverage**, they satisfy:

```
Ex(prefixL, live_vars_at (liveness_analyze fn) succ a) /\
Ex(prefixD, live_vars_at (liveness_analyze fn) succ a) /\
(!k. a <= k /\ k < LENGTH sb.bb_instructions ==>
  Ex(prefixL,(EL k sb.bb_instructions).inst_outputs) /\
  Ex(prefixD,(EL k sb.bb_instructions).inst_outputs))
```

This is a proposed sufficient interface, **not known true**. Dead residual
outputs on a revisit are a reason to scrutinize its universal output clause.
The endpoint's shared suffix witnesses must be the same ones satisfying
these exclusions; separately existential decompositions do not compose.
For a join without PHIs one needs the corresponding post-clean common-core
boundary; the cited PHI theorem explicitly assumes nonempty collected PHIs.

If S is too strong, the narrower alternative is actual stage query equality:
for every paired native ordinary prefix, immediately before optimistic swap,
`q = Var (LAST next_live)` either hits the current shared suffix or is absent
from both current residual prefixes (when the query is enabled). Even that
hit-or-exclusion condition is only sufficient; direct equality of observed
depths can hold in additional cases. A proof must use actual intermediate
states after emit/reorder/release, not entry coverage. This alternative needs
a strategist-designed statement with the actual stage equations; this audit
does not invent a replacement reachability invariant.

## Noncircular integration order and recommended next milestone

1. Native-only chronology/resource production T+N, with entry initialized by
   EntryProduction, unique predecessor U, and predecessor-indexed PHI resource
   transfer (`generate_phi_plan_live_budget`). Keep the successful DFS
   trace's saved and current inventories distinct. Establish a fresh block
   worker boundary, not another collection of conditional per-op facts.
2. From independently certified native budgets, terminal JMP residual-zero
   can give native incoming live exclusion. This alone does not give runtime
   residual-output exclusion or whole-stack equality.
3. Separately assess/prove S or its actual-query replacement along lineage
   edges. Reuse already checked paired PHI schedule replay; no runtime global
   output freshness is required for that particular consumer.
4. Compose block cleaning, parameter setup, PHI schedule, ordinary worker and
   terminal behavior, aligning cleanup height/promises existentially. Only
   after the necessary boundaries are validated may frozen theorem work begin.

**Recommended next coarse milestone for strategist review:** a native-only
successful-DFS incoming/worker certificate T+N with explicit entry, single
predecessor and PHI/JMP transitions. Before authorizing its implementation,
resolve whether live unit budget survives every PHI schedule and whether the
candidate native initialization at a join supplies the PHI selection inputs.
In parallel conceptually (not authorization for sibling work), classify S as
provable, overstrong, or requiring a narrower observation relation. It is the
smallest remaining *runtime semantic* gap; more primitive resource lemmas
will not by themselves close it.

Circular route rejected: use frozen block replay to get runtime poststates,
assert chronological unvisitedness at revisits, obtain fresh outputs, then
invoke ordinary replay to prove frozen block replay. The lineage constructor
already grants only the *previous* block replay and permits backedges;
CallTrace's visited-head case performs no recompilation. Native freshness
and runtime observation replay therefore have different induction indices.

## Residual obligations / verification

Unresolved: T+N global closure, U edge packaging, native PHI schedule resource
inputs, S physical shielding (or replacement), joins without PHIs,
unique-edge runtime relation, setup-to-worker composition, cleanup choices,
and terminal full-block integration. No counterexample to the frozen theorem
was established by this audit. Demand exclusion in ReturnCut is not physical
absence. Common live spills are allowed in ordinary replay; empty spilling
is a consequence at analyzed join JMP boundaries only.

Source endpoints inspected: CallTrace 6-40 and 145-228; Callers 112-164 and
489-569; EntryProduction 42-77, 518-640, 708-835; ChronologicalPrefix 7-117;
PhiLiveBudget 34-90; PhiTemporal 193-221; Edge 50-155; main Lineage 41-129,
630-721; ReturnCut 191-235. All paths are under `venom/codegen/proofs/`.

Validation: helper targets `fnPlanLineageChronologicalPrefixTheory`,
`fnPlanLineagePhiLiveBudgetTheory`, and integration target
`fnPlanLineageTheory` build successfully. The frozen final theorem's existing
admission remains unresolved; this diagnostic does not claim zero admissions
or task completion. Only this Markdown file is added by the audit.

## PHI boundary probe result (C3.bridge.2.phi_boundary_probe)

Checked in `fnPlanLineagePhiBoundaryProbeTheory`; this is a diagnostic
correction to candidate N above, not a counterexample to the frozen theorem.

1. Shared incoming uses across distinct PHIs: reuse TargetProbe's
   `repeated_target_disjoint_obstruction` and `repeated_target_ready_flags`.
   That fixture fails `phi_uses_disjoint`/`phi_operands_ready`; it is not an
   admissible successful native execution. This rejection does not prove
   general target-list distinctness.
2. Selected input also used after the PHI region: EntryProbe's
   `entry_live_input_rejected` checks `~phi_operands_ready entry_live_input_fn`
   for PHI x=(L:a,R:b) followed by ADD x,a. This proposed fixture is rejected,
   not evidence of a ready runtime mismatch. No general impossibility claim
   about all live-through configurations is inferred from it.
3. Dead PHI output: `phi_boundary_dead_ready` and `phi_boundary_dead_plan`
   certify readiness and SOME analyzed function planning. Actual predecessor
   calls and join calls succeed (`phi_boundary_dead_native_calls`). Cleaning
   and parameter preparation emit [] and preserve each incoming state.
   `phi_boundary_dead_frontiers` and `phi_boundary_dead_counts` measure:

   | frontier | analyzed live | stack from L / R | spill maps | counts (a,b,x) |
   |---|---|---|---|---|
   | predecessor JMP result / join setup / PHI prefix 0 | [a;b] | [a] / [b] | empty / empty | (1,0,0) / (0,1,0) |
   | PHI prefix 1 / ordinary start | [] | [] / [] | empty / empty | (0,0,0) / (0,0,0) |

   There is one PHI, so these are all its schedule frontiers. In particular,
   `native_live_boundary` is false at position 0 on both incoming paths and
   true at position 1. Ordinary union live coverage at *every* PHI position
   is therefore not a viable native certificate, even on a ready successful
   plan with empty spills and no duplicate physical cells.

### Boundary contract to design next (not a new HOL invariant)

Initialization must select incoming demands using the actual predecessor and
retain multiplicities of its actual JMP target list. At PHI prefix k, required
coverage must distinguish remaining predecessor-selected incoming operands
from already-written outputs still demanded by the suffix; it must not require
other predecessors' inputs or outputs not yet written. Physical counts and
origin support must be tracked separately from membership, with native output
freshness justified by chronological support. At the end of the PHI schedule,
the ordinary analyzed-live coverage/budget interface can resume; this fixture
checks that endpoint but does not prove it universally.

Existing consumers remain `generate_phi_plan_live_budget` (conditional native
physical selection/freshness) and `native_chronological_prefix` (ordinary
position interface). Existing paired schedule replay supplies runtime PHI
alignment, not native initialization. Missing universal implications remain
actual predecessor setup to selected frontier, PHI-prefix frontier transport,
and the ordinary endpoint to successful-DFS T+N closure. Unique-edge U and
runtime query shielding S are unchanged unresolved obligations. No global
induction or further conditional PHI lemma family was attempted here.

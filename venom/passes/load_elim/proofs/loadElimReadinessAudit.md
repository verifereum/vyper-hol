# Five-round readiness discharge audit (.42)

Diagnostic only; no new HOL obligations or assumptions are introduced here.
The frozen theorem and relations remain unchanged. Checked conditional execution
is not yet five-round correctness. Helper build: `loadElimCoupledExecutionTheory`
passes (2026-11-09, TO_load-elim-correct2-20261109T010004Z_m5359_t001).

## Exact consumer and actual rounds

Source of readiness: `loadElimCoupledExecutionScript.sml:70-93`.
The checked consumer at lines 941-953 has signature

```
le_round_ready C fn ctx s0 /\ le_padded_control V s0 t ==>
  (?e. run_blocks fuel C fn s0 = Error e) \/
  lift_result (le_padded_control V) (padded_exec_equiv V)
    (padded_exec_equiv V)
    (run_blocks fuel C fn s0)
    (run_blocks fuel C
      (analysis_function_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn)
          (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn)
            (load_analyze ctx fn) fn) ll inst]) fn) t)
```

Here V is exactly `{v | isPREFIX "$le_phi_" v}` (notation in this report,
not an extra theorem parameter). To obtain `load_elim_one`, specialize m to
`fn_max_inst_id fn` and unfold `load_elim_one_def` (defs:520-529). This also
requires its explicit `ir_cfg` to equal `cfg_analyze fn`.

The *actual* five calls (defs:554-582), writing f0 = fn and fi for fn1..fn4,
are as follows. All use g = cfg_analyze f0 and b = bp_analyze g f0;
A_M/A_T/A_S are analyses of f0, never of the intermediate functions.

| source | config | aliases supplied | DFG supplied | explicit CFG |
|---|---|---|---|---|
| f0 | memory_config | A_M = memory_alias_analyze b f0 | dfg_build_function f0 | g |
| f1 | transient_config | A_T = transient_alias_analyze b f0 | dfg_build_function f1 | g |
| f2 | storage_config | A_S = storage_alias_analyze b f0 | dfg_build_function f2 | g |
| f3 | dload_config | A_M | dfg_build_function f3 | g |
| f4 | calldataload_config | A_M | dfg_build_function f4 | g |

The fifth output f5 is subsequently passed to clear_nops_function. Each round
starts from the *same initial state s*, not the previous run's final state.
Cross-round result transitivity does not transport source invariants at s.

## Premise-by-premise matrix

A = exact checked theorem; B = elementary definition/specialization, with
premises identified; C = missing interface, not claimed derivable now.
The later column applies separately to f1, f2, f3 and f4 unless stated otherwise.

| readiness clause (line) | initial memory round f0 | later rounds f1..f4 |
|---|---|---|
| wf_function (72) | B: frozen premise | C: per-round wf preservation needed |
| fn_inst_wf (72) | B: frozen premise | C: replacements/inserted PHIs must be inst_wf |
| wf_ssa (72) | B: frozen premise | C: per-round **wf_ssa**, not merely ssa_form |
| le_configured_context (73) | B: mk_load_context_def + memory config equations + le_configured_context_def | B: same finite membership for each of four configs; independent of source function |
| ctx.lctx_dfg = dfg_build_function source (73) | B: record projection | B: record projection; does NOT imply DFG soundness |
| all bp_get_ptrs empty (74) | A/B: le_step_preserves_analyze_empty, instantiate bp/dfg to frozen analyses and s to initial s | A/B: identical b is reused; original empty-BP fact suffices, no recomputation |
| wf_alias_sets aliases (75), generalized in .45 | A/B: le_function_alias_maps_wf, mk_load_context_def | A/B: the same theorem covers A_T, A_S and A_M for every later source and configured address space; no reanalysis equality is required |
| entry label = SOME s.current_bb (76) | B: frozen premise | A: le_round_entry in loadElimRoundStructure; unconditional, arbitrary explicit CFG |
| load analysis fixpoint (77-80) | A/B: le_load_analyze_fixpoint + le_solver_process_def, using wf_function f0 | A/B conditional on wf_function fi; fixpoint theorem itself works for any ctx, no alias equality needed |
| dfg_assigns_sound rebuilt DFG s (81) | B: frozen premise | C: new ASSIGN chains and PHI definitions change DFG; original DFG soundness is not this fact |
| bp_ptr_sound b s (82) | B: frozen premise | B: exactly same b and s |
| alloca_inv s (82) | B: frozen premise | B: exactly same s |
| allocas_in_word s (82) | B: frozen premise | B: exactly same s |
| bp_ptrs_bounded b source s (83) | B: frozen premise | B: unfold bp_ptrs_bounded_def using empty bp queries; source dependence then vacuous |
| le_step_preserves b rebuilt_DFG source (84) | B: unfold le_step_preserves_def and le_step_invariants_def; precisely frozen universal-step premise | C: universal premise ranges over new PHI/ASSIGN/NOP instructions and rebuilt DFG; original premise covers only original instructions and original DFG |
| successful PHIs preserve rebuilt DFG (85-89) | B: precisely frozen PHI premise | C: augmented batches and rebuilt DFG; original premise does not quantify over these |
| prefix freshness of fn_all_vars (90) | B: frozen premise | C: NOT a preservation invariant: a successful inserting round introduces variables with this prefix |
| no MEMTOP in source (91) | B: EVERY_MEM + frozen premise | A: le_round_no_memtop in loadElimRoundStructure, using configured context |
| context functions no MEMTOP (92) | B: EVERY_MEM, frozen premise | B: execution context C is unchanged in all five calls |

Initial `le_padded_control V s s` is B by padded_exec_equiv_refl and
le_padded_control_def. Index-zero is a frozen premise; it is not a conjunct
of readiness. Initial LENGTH memory bound is not a readiness conjunct either.
Do not attempt to propagate it as a per-step invariant.

### Exact BP-empty discharge (not an assumed no-ALLOCA premise)

`loadElimBPEmptyScript.sml:182-189` proves:

```
fn_inst_wf fn /\ le_step_preserves bp dfg fn /\
bp_assigns_stable bp dfg /\ dfg_assigns_sound dfg s ==>
  (!v. bp_get_ptrs (bp_analyze cfg fn) v = [])
```

All four antecedents are frozen hypotheses, after packaging the universal-step
premise using SentinelHelpers:176-190. cfg may be the actual original CFG.
Its proof derives no-ALLOCA with le_step_preserves_no_alloca before applying
le_bp_analyze_empty. Thus merely quoting the latter is unnecessary/insufficient.
Original bp_phis_closed and bp_assigns_stable are not separate readiness
conjuncts; stability is used in this discharge.

## Reusable boundaries and exact mismatches

* **Aliases:** memAliasProps:34 `ma_analyze_wf` proves, for every bp/fn/space,
  `wf_alias_sets (ma_analyze bp fn space)`. At :43 `ma_may_alias_iff` proves
  `wf_alias_sets sets ==> (ma_may_alias sets l1 l2 <=> may_overlap l1 l2)`.
  These are exported interfaces (proofs also in memAliasProofs:496,505).
  Thus all three original alias maps already have the query semantics needed
  for *any* locations, independently of the later function/address space.
  Exact **map equality** to reanalysis is overly specific and not supplied.
  Minimal replacement: generalize semantic consumers from analysis equality
  to wf_alias_sets (or query soundness); do not assert map equality. Check all
  downstream consumers before changing that interface.
* **CFG:** cfg_analyze_def (cfgDefs:381) depends on labels, ordered blocks,
  entry, and successors. Per-round preservation of these would give full CFG
  equality, including DFS order. cfgAnalysisProps:96 only gives successors
  of an existing block under wf; it is not transformation invariance.
  `analysis_function_transform_prepend_def` (analysisSimDefs:249) merely maps
  blocks. No load_elim_one CFG equality theorem was found. Until it is proved,
  the explicit g in load_elim_one is not the internally recomputed CFG in
  le_coupled_run_initial.
* **Structural preservation:** loadElimWf:15,26 contains inherited cheats for
  whole-pass wf_function and ssa_form, not checked per-round wf_ssa/inst_wf
  interfaces. These cannot discharge the matrix. Their independent task is
  acknowledged in TASK; no reliance on them is made here. Shared/simulation
  searches and load_elim_one theorem search found no equivalent round theorem.
* **Source agreement/fresh names:** ReachedSourceAgreement:8-32 proves
  generation/singleton Var membership in fn_all_vars; :66 onward provides
  selected source values. The bridge to outside-prefix lookup agreement uses
  source prefix freshness. On fi, existing generated variables are genuine
  source operands and must agree, not be discarded as exceptions. Minimal
  replacement is a per-round generated set disjoint from the current source
  variables (with source-domain agreement), rather than global prefix
  freshness. Future rounds may generate names with the *same* prefix. Prove
  disjointness via distinct original load ids/disjoint load opcode classes;
  do not assume that fn_max_inst_id alone makes fresh_phi_var names fresh.
* **Rebuilt DFG:** dfg_assigns_sound is a state-dependent equality invariant,
  not a consequence of wf_ssa. OccurrenceInvariants:26,39,59 carries it only
  after receiving PHI/step preservation for the same DFG and function. It
  cannot produce those universal premises for fi. A boundary deriving the
  particular normalized-operand validity needed on reached fi executions
  from earlier coupling may avoid requiring universal new readiness. This
  is an integration design question, not a checked fact of this audit.

Search scope: load_elim helper theories, shared pass props, simulation props,
analysis CFG/DFG/mem-alias, memory_copy_elision, and project theorem search
for load_elim_one, analysis_function_transform_prepend, cfg transformation,
ma_analyze/wf and lift_result. Negative results above mean no matching checked
consumer interface was located, not a claim of mathematical impossibility.

## Padded-result composition and clear_nops

A: MemoryRel:19 has exact signature
`padded_exec_equiv V a b /\ padded_exec_equiv V b c ==> padded_exec_equiv V a c`.
B: le_padded_control transitivity follows by adding its three control equalities
(PaddedNoncall:6). It is definitionally the frozen le_state_equiv when both
padded_exec_equiv and frozen le_exec_equiv are unfolded. The execution relations
are likewise identical; no change to frozen definitions is required.

B (not yet packaged as an exported load-elimination theorem): lift the two
transitivities by cases on the three exec_results using lift_result_def,
retaining the source-Error disjunct. In the non-Error branch the first relation
forces the intermediate result to be non-Error of the same constructor, so
an intermediate source-Error disjunct is impossible. Abort tags and IntRet
values compose by equality. No new semantic invariant is involved.
Existing deadStoreElimProofs:148 `lift_result_or_error_trans` is **local** and
uses the *same* R for all three result positions, so it cannot simply be
imported for the control/terminal distinction. Do not duplicate its whole
pass-specific machinery; a small three-relation boundary would suffice.

A: passSharedProps:905:
`wf_function f /\ s.vs_inst_idx = 0 ==> result_equiv {}
 (run_blocks fuel C f s) (run_blocks fuel C (clear_nops_function f) s)`.
C: for f5 the required wf_function f5 still needs per-round structural proof;
whole-pass wf after clearing does not imply this pre-clear premise.
B: result_equiv {} weakens to the padded lifted relation at V, by exact memory
and frame equality and full variable agreement (stateEquiv:119,158,173).
This is elementary constructor/definition reasoning, not yet an exported
load-elimination bridge. It composes with the five rounds once readiness gaps
are closed. No further memory-length or no-MEMTOP premise is required by the
clear_nops theorem itself.

## Recommended finite next semantic milestone (proposal, not authorization)

Before extending final execution proof, validate a **round-domain interface**:
(1) replace exact alias reanalysis with wf_alias_sets/query semantics, using
the already exported unconditional alias theorems; (2) expose source-variable
agreement and generated-set disjointness instead of global-prefix freshness.
First prove small currentness/selected-input consumers with these interfaces,
then review the affected coupling contract. Separate per-round structural
CFG/wf_ssa/inst_wf preservation from reached rebuilt-DFG validity; do not hide
either in generic preservation assumptions in a final wrapper. A successful
initial-memory readiness specialization alone will not settle these gaps.
No final-theorem proof or speculative helper stub has been added in this audit.

## Checked alias-query integration (.45)

The exact-reanalysis conjunct described above is now historical. The current
`le_round_ready` requires only `wf_alias_sets ctx.lctx_aliases`; all other
conjuncts are unchanged. `le_coupled_run_initial` and the full dependency cone
build under this generalized contract (2026-11-09,
TO_load-elim-correct2-20261109T010004Z_m5407_t001).

Inventory: the only implementation-level use of a specific analyzed map was
`le_retained_store_read_step` in RetainedStore. It obtained well-formedness by
`ma_analyze_wf` before applying `le_retained_store_regions`, which already uses
`ma_may_alias_iff`. Both store read/key-read boundaries now accept an arbitrary
well-formed alias map. No representation-dependent use was found. Propagation
changes only hypotheses in SingletonCurrentness, ExitCurrentness, LatestRead,
HomogeneousCurrentness, LatestRetention, ReachedAvailability, ReachedCapture,
ReachedSourceAgreement (including domain/disjoint/prefix corollaries),
ReachedBatchSuccess, ReachedStore, ReachedLoad, DynamicCapture, ActualPhiFrame,
CaptureEntry and CoupledExecution. Existing proofs replay without tactical
changes. The 16-theory integration build passed in
TO_load-elim-correct2-20261109T010004Z_m5404_t001.

`le_function_alias_maps_wf` specializes the existing generic `ma_analyze_wf`
through the three alias-analysis wrappers, so the original A_M/A_T/A_S maps
satisfy readiness's alias clause regardless of later source or address space.
It does not assert equality to reanalysis. The final coupled theory build also
checks this specialization. This discharges the alias row only: generated-name
disjointness/source-domain coupling, CFG and structural preservation, rebuilt
DFG validity and later-source step/PHI invariants remain unresolved. No frozen
statement, relation, or final proof has been changed.

## Checked round-local name integration (.46)

The prefix-only consumer displayed in the original audit is now a compatibility
specialization of `le_coupled_run_initial_disjoint`. The latter uses arbitrary
`G` in the incoming `le_padded_control` and all three lifted result relations.
Its readiness is `le_round_ready_disjoint G m C fn ctx s0`, defined by:

* `le_round_ready_names G C fn ctx s0`: every original non-name readiness
  conjunct, with source prefix freshness replaced by
  `DISJOINT G (set (fn_all_vars fn))`;
* every action collected for this round has its `pa_phi_out IN G`.

`le_round_ready C fn ctx s0` remains the prefix specialization of the first
predicate. For it, output containment follows from
`le_collected_action_output_prefix`, so the original exported
`le_coupled_run_initial` needs no additional premise. The execution induction
is shared, not duplicated. Build evidence: 2026-11-09,
TO_load-elim-correct2-20261109T010004Z_m5472_t001.

The migrated cone includes batch totality, DynamicCapture, ActualPhiFrame,
CaptureEntry, TargetWrites, CaptureSteps and ReachedLoad. Selected snapshot
transport uses the already checked source-domain/disjoint capture interfaces.
Source writes are excluded by source-domain nonmembership; generated writes
are invisible by collected-output containment. No instruction-level target
preservation assumption, successful target suffix or final-theorem premise
was added. ReachedStore was already generic in its memory relation.

This discharges only the **conditional semantic use** of round-local names.
For actual later rounds the following remain unproved and must not be hidden
by specialization to the whole reserved prefix:

1. Choose each round's `G`, prove it disjoint from that round's current source
   variables, and prove containment of that round's collected outputs. Names
   generated in earlier rounds are now source variables and must agree.
2. Prove per-round CFG/entry preservation so the wrapper's reused original CFG
   matches the analysis CFG of each intermediate source.
3. Prove per-round wf_function, fn_inst_wf, wf_ssa and no-MEMTOP preservation.
4. Establish soundness of rebuilt DFG at the common initial state and the
   PHI/step preservation hypotheses for reached intermediate executions (or
   replace this readiness interface through a separately validated design).
   Result transitivity and wf_ssa alone establish none of these DFG facts.
5. Package result composition and the clear_nops bridge with their structural
   hypotheses discharged. The frozen final theorem remains untouched.

## Checked round structure (.47)

`loadElimRoundStructureTheory` builds at the default tactic timeout. Its public
wrappers are `le_round_cfg`, `le_round_entry`, and `le_round_no_memtop`.
`le_round_cfg` requires only `le_configured_context ctx` and accepts any explicit
CFG `g`; the entry wrapper is unconditional. Internal `le_prepend_cfg` and
`le_prepend_no_memtop` accept arbitrary analysis results and arbitrary actions.
The successor proof covers empty and all-PHI blocks, not just well-formed
terminator-ending blocks. CFG equality follows from identical labels and block
successors, without unfolding DFS. The existing `fn_insts_EVERY_block` from
`ctxLookupAgreeHelpers` is reused rather than duplicated.

Thus the original explicit CFG is suitable at every later round once its context
is configured. This does not prove wf_function, fn_inst_wf, or wf_ssa preservation,
new-name disjointness, nor any rebuilt-DFG semantic readiness clause. Those remain
separate obligations; neither structural equality nor opcode exclusion supplies
them. The frozen target and the accepted arbitrary-G execution proof are unchanged.

## Rebuilt-DFG diagnostic (.48): checked obstruction and consumer contract

`loadElimDFGReadinessProbesTheory` builds at the default timeout (2026-11-09,
TO_load-elim-correct2-20261109T010004Z_m5575_t001). Its source is a single block
`x = MLOAD 0; y = MLOAD 0; STOP`. `readiness_probe_wf` checks wf_function,
fn_inst_wf and wf_ssa. The context is the **actual** memory context, with
bp_analyze and memory_alias_analyze of that source, not arbitrary empty maps.
`readiness_probe_round` checks that load_elim_one replaces the second MLOAD
by `y = ASSIGN x`, and `readiness_probe_rebuilt_lookup` checks its DFG entry.

At the shared initial state, x=0 and y=1. Original DFG soundness holds for
**every** state (`readiness_probe_source_sound`): there are no ASSIGNs.
`readiness_probe_rebuilt_unsound` refutes rebuilt soundness by specializing
its universal definition to y and its actual ASSIGN, then evaluation. The
combined `readiness_probe_no_initial_transport` includes the structural facts,
original initial DFG soundness, and the **full frozen universal-step premise**,
packaged as le_step_preserves with the original analyses. Thus that premise
itself does NOT exclude this auxiliary example. MLOAD only updates variables;
STOP has no OK result, and allocation-field predicates are unchanged. Empty
BP queries are checked separately by readiness_probe_bp_empty.

This is not frozen-theorem falsehood: no mismatch of original/transformed
run_blocks is claimed; all frozen premises have not been certified together.
The newly introduced equality becomes true after the second instruction has
executed, but is not true at the initial state or necessarily just after the
first MLOAD. Global rebuilt soundness, even at *every reached point*, is the
wrong sufficient invariant to try to transport across rounds.

### Direct normalization consumer map

All entries below use d = ctx.lctx_dfg and N(op) = normalize_operand d [] op.
These are precise semantic use sites, distinct from wrappers merely carrying
DFG hypotheses. Line numbers refer to current source, not this document.

| consumer | state/domain actually used |
|---|---|
| ConfiguredGeneration:69,75 (`le_configured_generation_read`) | generating StepOcc input u: N(addr) evaluates like addr, for the actual load/store address |
| SingletonCurrentness:89 (`le_configured_retained_step_read`) | retaining store input u: N(op1) evaluates like the actual store address op1, to justify invalidation/non-aliasing |
| SingletonCurrentness:144,158 (`le_configured_generation_address`) | generating input u: same load/store address normalization, to identify actual key address |
| HomogeneousCurrentness:282 | selected generator post-state t: N(op)=r implies eval op t = eval r t; op is the generated operand (load output or store value), NOT an arbitrary alternative |
| HomogeneousCurrentness:367 | final store input s: N(value) evaluates like the actual store value; combined with selected historical generation, not all alternatives evaluated at s |
| ReachedStore:106 (`le_empty_store_key_read`) | current store input s: normalized actual address agrees with address |
| ReachedLoad:46 (`le_empty_configured_load_address`) | current load input s: normalized actual address agrees with address, including the DLOAD case |
| StoreEquivalence:14 | at its caller state s, two compared Var operands a,b each need normalization validity; this helper has no external caller in the current cone (grep), so do NOT make all-alternative currentness a new global premise on its account |

Initial/PHI/step/snapshot separation: OccurrenceInvariants:139-182 derives
whole-trace pre/post DFG soundness from initial soundness, universal step
preservation and reachable PHI preservation. ReachedLoad/ReachedStore use that
wrapper; it cannot re-create new equalities for a rebuilt DFG. CoupledExecution
readiness:81,84-89 packages those three requirements, and :765 extracts the
PHI-prefix soundness requirements for CaptureEntry. ReachedAvailability,
ReachedCapture, DynamicCapture, ActualPhiFrame, CaptureEntry and
ReachedSourceAgreement thread historical step DFG facts to generation/read
consumers. Generated PHI selection itself reads the **incoming snapshot** u;
no normalize_operand call occurs in capture. It needs the selected historical
value, derived from generation plus retained suffix, then incoming lookup
agreement. Normalizing every PHI alternative in u is neither required nor
justified. Original PHI results p are subsequent body-input states and should
receive only the reached-use obligations of their actual later consumers.

### Candidate replacement contract (proposal only, no new assumptions)

Reuse `loadElimNormalizeHelpers.le_chain_valid d [] op s` and its checked
`le_chain_valid_eval`, rather than inventing another normalization predicate.
This existing recursive predicate restricts ASSIGN equalities to the chain
actually traversed from op; non-Var, missing definitions, non-ASSIGNs and
visited-cycle stops impose no further equalities. The library restricted
normalize_operand_eval theorem instead quantifies over ALL unvisited defs;
visited=[] is not a reached-use solution. Search of shared/simulation/analysis
and memory-copy-elision found only the global/restricted eval interfaces and
local memory-copy operand_equiv facts, not a reached-domain discharge theorem.

For each actual le_occ_prefix of intermediate source fi, a sufficient exact
consumer contract would assert the following, with d = dfg_build_function fi:

1. At every successful StepOcc bb n fuel u t, for actual configured load
   operands [addr] or store operands [addr;value], require
   `le_chain_valid d [] addr u`. This covers generation, retention/invalidation,
   and active load/store address identification. At the current prefix end s,
   the same applies to its active load/store when successful evaluation is used.
2. For each **selected generating event** whose syntactic generation operand
   op feeds the historical singleton/homogeneous certificate, require
   `le_chain_valid d [] op t` at its post-state. This is the extra post-state
   fact at HomogeneousCurrentness:282; input-only validity does not replace it.
3. At a reached redundant-store test on actual value operand value, require
   `le_chain_valid d [] value s`. Together with (2) and the checked retained
   representative no-write argument, this yields store-test currentness.
4. For a requested pre-PHI snapshot capture, use (1)-(2) on the historical
   selected generator/retained suffix ending in that snapshot. Do NOT require
   all alternatives' chains at the snapshot, nor normalize original PHIs'
   incoming variables in their post-PHI state. Existing source-domain incoming
   agreement remains a distinct requirement.

These clauses deliberately quantify selected historical generators, not all
members of a multivalue lattice at a current state. Literal-only initial
instructions satisfy address validity without constraining not-yet-written y.
A useful implementation may strengthen (1),(3) to validity for **all actual
instruction operands at their reached use**, but must retain selected generator
post-state validity (2). No need for validity at unused initial outputs.

Discharge route still to be proved: SSA def-dominates-use plus successful
execution must provide an occurrence of each relevant ASSIGN before the
actual use, and absence of intervening redefinitions until that use. Follow
the normalization chain with a visited set; when a chain source is itself
assigned, order/dominance must justify its defining occurrence too. For the
post-state load output in (2), its definition is the just-executed load (not
ASSIGN); a store value is an actual input whose chain facts must survive that
store. Across rounds, prior-round coupling constructs executions of fi from
successful earlier executions, including introduced ASSIGN execution and PHI
snapshot availability. It does NOT transport global DFG soundness at shared s.
Loops require occurrence/epoch reasoning: static uniqueness is not absence of
dynamic reexecution. Full structural wf_ssa, round-local name separation and
source-error handling remain separate obligations. Proving these reached-use
clauses and refactoring the cone needs a reviewed follow-up PLAN; none is
asserted proved, inserted as a target hypothesis, or implemented here.

## Dynamic discharge audit (.51)

This section is a signature/source audit, not a new HOL theorem or a change
of readiness. The current `loadElimCoupledExecutionTheory` dependency cone
was checked by holbuild (nothing needed rebuilding); no SML was changed.

### Finite replacement-premise matrix

Use d = ctx.lctx_dfg = dfg_build_function fn. `I(j,u)` below abbreviates
`le_inst_operands_valid d j u` only in this prose. `P(key,es)` abbreviates
`!bb n k u t op. MEM (StepOcc bb n k u t) es /\
 le_transfer_generates ctx (EL n bb.bb_instructions) key op ==>
 le_chain_valid d [] op t`. Neither abbreviation is a proposed definition.

| Exported consumer | Exact normalization use | Checked local replacement | Still missing in wrapper |
|---|---|---|---|
| `le_configured_generation_read` | generating load/store address at input u | `le_configured_generation_read_local` takes I(j,u) | reached input validity |
| `le_configured_generation_address` | same address, identifying key address | `le_configured_generation_address_local` takes I(j,u) | reached input validity |
| `le_configured_retained_step_read`, multivalue variant | retaining store address at input u | respective `_local` exports take I(j,u) | reached input validity |
| `le_retained_occ_read`, `le_prefix_retained_suffix_read` | those same addresses on a retained interval | respective `_local` exports quantify I over StepOcc inputs | validity on every relevant step, not just the final consumer |
| `le_occ_prefix_singleton_current`, `le_frame_singleton_current` | generation and retained reads; singleton operand is transported without normalizing it | respective `_local` exports, occurrence-wise I | discharge I; no new all-alternatives post-state requirement |
| `le_occ_prefix_homogeneous_current` | generation/retention input addresses AND selected generation op at post-state t | `le_occ_prefix_homogeneous_current_local`, occurrence-wise I plus P(key,es) | I and selected post-chain discharge independently |
| `le_occ_prefix_store_test_current` | homogeneous representative as above AND normalize actual current store value at s | no exported local store-test wrapper yet; homogeneous `_local` plus `le_inst_operands_valid_eval` provide ingredients | I on historical events, P(key,es), current I(i,s); actual `[addr;value]` membership must be exposed |
| `le_empty_configured_load_address` (ReachedLoad:35-54) | normalize actual addr at s, including special DLOAD branch | no local export yet; replace only its DFG-to-eval step by operand-validity evaluation | current I(i,s), or simply chain validity of addr |
| `le_empty_store_key_read` (ReachedStore:94-112) | normalize actual addr at s | no local export yet; same replacement | current I(i,s), or chain validity of addr |
| `le_reached_singleton_load_replacement` | current load address plus historical singleton currentness | local constituents above checked, reached wrapper not migrated | current I plus historical I; other static, padded agreement and success premises unchanged |
| `le_reached_captured_load_replacement` | current load address; capture persistence uses historical reads | local address wrapper still absent; capture itself has no normalization | current I and historical I wherever capture generation/retention uses them |
| `le_occ_prefix_frozen_store_test_current`, `le_reached_store_replacement` | historical homogeneous value and current address/value | constituents above, no exported local reached wrapper | historical I, P(key,es), current I; do not retain rebuilt global initial soundness just to invoke the frozen wrappers |
| `le_occ_prefix_phi_selected_value` and exit-currentness/availability wrappers | selected historical singleton generation and suffix reads to pre-PHI snapshot | singleton `_local` interface available; these wrappers still thread DFG facts | historical I; actual predecessor, selected input availability and source-domain agreement remain distinct |
| ReachedCapture, ReachedSourceAgreement, DynamicCapture, ActualPhiFrame, CaptureEntry | no additional direct normalization; consume the preceding selected-value/read contracts | accepted conditional snapshot and source-domain interfaces | migrate threaded historical facts after dynamic discharge, not by assuming transformed PHI success |
| `le_round_ready_names`, coupled changed step, PHI entry, block/run wrappers | package/extract global initial, PHI and universal-step DFG conditions for the above wrappers | none: readiness intentionally unchanged | a validated trace-local replacement and downstream migration; BP/allocation and naming/static conditions are separate |
| `loadElimStoreEquivalence` helper | normalize two compared operands at its supplied state | `le_chain_valid_eval` for each operand | no current caller in this cone; no reason to require all alternatives current |

The `_local` homogeneous signature currently requests P for **every generating
StepOcc for this key in es**. Its proof selects one such event via
`le_occ_prefix_homogeneous_suffix`. A future narrower selected-event interface
could reduce the quantification, but is not present or assumed in this audit.

### Checked dynamic interfaces (exact relevant signatures)

* `loadElimLastWriter.le_occ_ssa_use_writer`:
  `wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
   fn_entry_label fn = SOME s0.vs_current_bb /\
   le_occ_prefix C fn s0 es i s /\ i.inst_opcode <> PHI /\
   MEM (Var v) i.inst_operands ==>
   ?e. MEM e es /\ v IN le_occ_writes e`.
  Thus an executed writer for an ordinary operand is already checked; it is
  not necessary to invent that conclusion from informal dominance.
* `loadElimLastWriter.le_occ_prefix_last_writer`:
  `le_occ_prefix C fn s0 es i s /\
   (?e. MEM e es /\ v IN le_occ_writes e) ==>
   ?pre e suffix. es = pre ++ e::suffix /\ v IN le_occ_writes e /\
   EVERY (\q. v NOTIN le_occ_writes q) suffix /\
   le_occ_valid C fn e /\ lookup_var v s = lookup_var v (le_occ_post e)`.
* `loadElimLastWriter.le_occ_writer_instruction` identifies a StepOcc writer's
  actual instruction and output membership, or a PhiOcc writer's member of
  the leading PHI prefix. With `ssa_form_output_unique` and DFG correctness,
  this is the route to identifying an ASSIGN writer as the specific DFG def.
* `loadElimOccurrence.le_occ_prefix_suffix_lookup`:
  `le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
   EVERY (\q. v NOTIN le_occ_writes q) suffix ==>
   lookup_var v s = lookup_var v (le_occ_post e)`.
* `loadElimOccurrence.le_occ_chain_lookup`:
  `le_occ_chain s es t /\ EVERY (le_occ_valid C fn) es /\
   EVERY (\e. v NOTIN le_occ_writes e) es ==>
   lookup_var v t = lookup_var v s`.
  These supply transport **given** no writes; they do not prove source no-write.
* `loadElimOperationalHistory.le_oper_history_interval_lookup` transports a
  lookup between history endpoints when `le_epoch prefix v =
  le_epoch (prefix ++ interval) v`. `le_epoch` counts write-footprint events,
  and `le_epoch_zero` is equivalent to EVERY nonmembership. This is not a
  separate temporal theorem establishing equality of the epochs.
* `passSharedProps.mk_assign_inst_correct`:
  `!fuel ctx inst src_op s v out.
   eval_operand src_op s = SOME v /\ inst.inst_outputs = [out] ==>
   step_inst fuel ctx (mk_assign_inst inst src_op) s =
   OK (update_var out v s)`.
  This is public construction semantics, not inversion of an arbitrary
  successful ASSIGN. Search found arbitrary-step inversion as
  `genBlockSim.step_inst_assign_ok`, but it is LOCAL. Public
  `phiBlock.step_inst_assign_eval` is a step_inst_base equation (opcode
  ASSIGN, operands [op], outputs [out]);
  `overflowElimHelpers2.step_inst_base_assign` inverts that base step.
  A small public full-step inversion/equality boundary may be needed locally;
  do not cite a local theorem from another theory.
* `loadElimNormalizeAvailability.le_available_via_definition` transports
  `def_available_at fn db (SOME di) v` through an available output u of di
  to `def_available_at fn bb point v` (wf_function, ssa_form, memberships).
  `le_normalize_operand_available` transports availability through the
  normalization recursion. These are static endpoint availability, not
  equality preservation between two dynamic occurrences.
* `venomWf.fn_dominates_def` quantifies entry-to-node paths; it does not assert
  anything about an arbitrary later source write in an occurrence suffix.
  `le_normalized_generator_available` proves output membership OR static
  availability of the normalized representative. `le_nonassign_output_normalize`
  proves that a non-ASSIGN output normalizes to itself. The normalized
  definition cuts exclude certain retained homogeneous lists at definitions;
  they do not prove all ASSIGN-chain equalities at an arbitrary use.

Search scope included shared pass properties, simulation operand agreement,
DFG correctness/restricted normalization, base occurrence/history helpers,
SSA/dominance/availability, and memory_copy_elision soundness. No searched
export discharges the source-epoch condition below. This is a bounded search
result, not a claim that no such theorem can exist anywhere in the repository.

### Proposed mathematical obligations (NOT checked, no SML stubs)

**A. Input-use discharge (missing).** A useful consumer-shaped theorem is:

```
wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
fn_entry_label fn = SOME s0.vs_current_bb /\
le_occ_prefix C fn s0 es i s /\ i.inst_opcode <> PHI
==> le_inst_operands_valid (dfg_build_function fn) i s
```

No initial variable equalities appear here. Literal, Label and non-ASSIGN
stops are trivially valid; arbitrary ordinary instructions are proposed to
avoid duplicating per-opcode reasoning. This statement remains unproved.
It must not be used as an assumption of the frozen theorem or silently added
to readiness. Stronger induction likely uses `def_available_at` for each
recursively followed Var, not only immediate operand membership.

**B. The missing dynamic source-epoch lemma.** For any actual prefix
`le_occ_prefix C fn s0 (pre ++ StepOcc db n k u t::suffix) i s`, assume
wf_function, fn_inst_wf, wf_ssa, entry equality; let
`di = EL n db.bb_instructions`, with
`di.inst_opcode = ASSIGN`, `di.inst_operands = [Var w]`,
`di.inst_outputs = [v]`, and
`EVERY (\q. v NOTIN le_occ_writes q) suffix`.
The needed new conclusion is
`EVERY (\q. w NOTIN le_occ_writes q) suffix` (or a precisely sufficient
weaker value-equality conclusion). No such conclusion follows from last-writer
selection alone. It requires a temporal dominance argument: every subsequent
write of w is the same static source definition; returning from that definition
to this reached use must revisit the ASSIGN defining v before reaching the
use, contradicting that v's selected occurrence was its last writer. The
consumer must have `def_available_at fn bb (SOME i) v` at its actual fetched
block bb (or the equivalent recursive availability premise). Include that
endpoint premise in a formal version of B; the arbitrary-prefix version
without an available consumer is NOT proposed as a theorem.

B must also account for same-block strict ordering, block revisits, the
possibility the selected v writer is in an earlier loop iteration, and sources
written by a PhiOcc. A path from the source definition to a use is not itself
an entry-rooted path: splice it with a first-arrival entry prefix avoiding the
v definition, or establish an equivalent cycle/order lemma. Existing
`le_fn_dominates_antisym` alone does not establish this temporal conclusion.
This is the exact remaining gap, rather than absence of any executed-writer
interface. After B, use successful ASSIGN semantics to establish
`lookup_var v t = eval_operand src u`; src is not an output (SSA plus strict
availability must justify that), hence its evaluation is unchanged by the
ASSIGN. Transport v and src to s and recurse on src with visited v. A Label
source needs label-frame preservation, not variable no-write; history operand
transport already exposes the separate label equality condition.

**C. Selected generator post-validity (missing general theorem).** For any
`MEM (StepOcc bb n k u t) es` in an actual le_occ_prefix and
`le_transfer_generates ctx (EL n bb.bb_instructions) key op`, under the same
structural/entry assumptions and configured ctx with rebuilt DFG, prove
`le_chain_valid ctx.lctx_dfg [] op t`.
For a generating load, op is Var out of a non-ASSIGN load; uniqueness and
DFG lookup identify a non-ASSIGN definition, so the chain predicate stops
immediately. The checked `le_nonassign_output_normalize` proves a syntactic
normalization fact, not this predicate, but its DFG identification proof is
reusable. For a generating store, op is the actual value input. Apply A at u,
then prove validity unchanged by the successful store: configured stores have
no outputs and preserve lookups, and their label frame is preserved. This is
not justified by I alone for arbitrary instructions that write their own
inputs. The `_local` homogeneous signature can then consume C for all its
key's generating events, without global post-state DFG soundness.

**D. Scope at PHIs.** Do NOT claim A for PHI operands at body-entry or in the
post-batch state. A PhiOcc is one snapshot batch with a union write footprint;
all incoming operands read u even when another PHI overwrites the same name
in t. If an ASSIGN chain uses a PHI-defined source, B must treat the whole
PhiOcc as its defining write and select the correct iteration. Re-entering a
header may refresh that source, so the prior ASSIGN equality can only be
transported after excluding such a refresh on the suffix, not just by static
SSA uniqueness. Generated PHI capture uses selected historical input value
and incoming snapshot lookup agreement; it never needs all alternatives'
chains in u or equality of incoming/post-PHI lookups. Accepted snapshot capture
and totality boundaries remain separate from A-C.

### Original-round compatibility and the E0212 boundary

CHECKED: `le_occ_prefix_frozen_dfg` (OccurrenceInvariants:161-182) derives
current soundness and pre/post soundness for every successful StepOcc from
the original initial DFG, full le_step_preserves, reachable PHI preservation,
empty-BP and allocation hypotheses. `le_dfg_sound_inst_operands_valid` yields
I at those inputs/current state; `le_dfg_sound_chain_valid` yields C at every
selected post-state. This original-round derivation therefore supplies every
normalization contract in the matrix once the other frozen hypotheses are
connected to that wrapper. It does not assert soundness solely from SSA.

DISPROVED route: for a rebuilt round, E0212's checked actual memory round
introduces `y = ASSIGN x` while initial x and y differ. Original global DFG
soundness and the original full universal-step condition hold in that probe,
but rebuilt initial soundness does not. Calling the same wrapper with the new
DFG would simply demand its false initial premise. A-C are intended to avoid
unused initial equalities entirely. Their general validity and multi-round
structural/name/analysis premises still require proofs, and prior-round
coupling alone does not establish them. No readiness definition, coupling
contract, frozen statement, or SML proof was changed by this diagnostic.

Audit disposition: checked local interfaces and last-writer machinery exist;
source-epoch transport and recursive reached-chain discharge remain MISSING,
not disproved. Review B and the stronger recursive availability interface
before authorizing wrapper migration or the final theorem.

## Temporal separator and occurrence interval audit (.52)

CHECKED: `loadElimTemporalDominance.le_dominating_separator` proves

```
fn_dominates fn a d /\ fn_dominates fn d b /\ a <> d /\
is_fn_path fn (a::tail) /\ LAST (a::tail) = b
==> MEM d (a::tail)
```

No wf, SSA, entry-rooted suffix or acyclicity hypothesis is hidden in this
statement. Dominance supplies reachability of a. A first-arrival entry path
to a avoids d (otherwise a would dominate that earlier d, contradicting first
arrival). Splicing it to the given suffix and using dominance of d over b
forces d into the suffix. The local splice lemma is not exported. The
separator is a graph result only: membership does not certify execution of
any particular instruction. Tail=[] and a=b are covered by the proof; in
particular a cycle cannot evade a genuinely intermediate dominator. No claim
of temporal source stability follows merely from this check.

### What the occurrence exports actually provide

* `le_occ_prefix_route` (OccurrenceCoverage:46) gives a nonempty entry-rooted
  path `le_occ_route es` ending at s.current_bb. The route records **PhiOccs**,
  not StepOccs. `le_occ_route_append` splits this list at event boundaries.
  A route suffix starting with a selected PhiOcc therefore gives a candidate
  source-block-to-consumer route. A source StepOcc does not itself contribute
  its label: its block label must be prepended to the later PhiOcc route.
  Extracting that path, including its first transition, needs a suffix-path
  lemma; `le_occ_prefix_route` alone is not such a lemma.
* `le_occ_suffix_positions` (OccurrencePositions:6) supplies the LAST label
  and an upper positional bound for events after a selected PhiOcc. It does
  not state a CFG path for that suffix, nor that every intermediate
  instruction is present in that suffix.
* `le_occ_prefix_current_coverage` and `_completed_coverage`
  (OccurrenceCoverage:110,162) do prove writes from instructions before the
  current index and from completed route blocks respectively. Their
  conclusion is `le_occ_wrote es v` for the **whole prefix es**. They do not
  locate that writer after an arbitrary selected event. Using them unchanged
  could choose the earlier selected ASSIGN and hence cannot contradict its
  being the last writer. `le_occ_prefix_close_coverage` has the same whole
  prefix limitation (and its appended step need not itself be certified OK).
* The inductive prefix rules supply full actual traversal: ordinary next
  increments the index, while block transition inserts a PhiOcc and resets
  the next body index to phi_prefix_length. `le_occ_prefix_valid` supplies
  actual fetched blocks for recorded events; `le_active_inst_lookup` plus
  `_prefix_active` supplies the fetched **consumer** block. These are the
  raw ingredients for interval coverage, not an exported interval theorem.
  The abstract `le_occ_chain` alone does not encode complete traversal.

### Exact missing interval interface (proposal, NOT a checked theorem)

A useful single consumer-shaped crossing interface, avoiding another history
relation, is the following. Quantify C, fn, s0, pre, e, suffix, i, s, db, di,
v, w, cb. Assume:

```
wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
fn_entry_label fn = SOME s0.vs_current_bb /\
le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
lookup_block s.vs_current_bb fn.fn_blocks = SOME cb /\
def_available_at fn cb (SOME i) v /\
MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
di.inst_opcode = ASSIGN /\ di.inst_operands = [Var w] /\
di.inst_outputs = [v] /\ w IN le_occ_writes e
==> ?q. MEM q suffix /\ v IN le_occ_writes q
```

The conclusion locates a destination write strictly **after** a source write,
not just somewhere in pre++e::suffix. Static uniqueness identifies the source
writer but does not discharge this conclusion. Source availability at di is
derived from wf_ssa's ordinary-use clause; the consumer availability must be
explicit for recursively followed normalization variables (immediate operand
membership at i is insufficient). No assumption that v was written earlier
is needed for this crossing proposal. If established, applying it to each
source-write event in the suffix after a last v writer yields audit B by
contradicting v's suffix nonmembership. This is a proposed interface for
review, not permission to assume it in readiness or the frozen theorem.

Case obligations for this interface:

1. **Distinct source/destination/consumer blocks:** derive source dominance
   over destination from the ordinary ASSIGN use; derive destination dominance
   over consumer from def_available_at and unique definitions. The checked
   separator forces destination block membership in the source-to-use route.
   If the visit is completed, interval (not whole-prefix) coverage must locate
   di's write after e.
2. **Destination equals consumer block:** block membership alone is vacuous.
   Availability and unique instruction IDs give di's index strictly before
   the fetched consumer index. Coverage of the final visit must locate that
   write in suffix, not a previous visit to the same label.
3. **Source and ASSIGN in the same block:** source availability gives strict
   source-before-ASSIGN order for an ordinary source definition. Starting at
   the source StepOcc, either traversal stays in the visit and crosses di, or
   completes the visit before leaving. Numeric indices cannot be compared
   across a re-entry without this split. A source write after an older ASSIGN
   occurrence may belong to a later visit; the crossing must still be in
   suffix.
4. **Re-entry:** every successor visit begins with PhiOcc and resets traversal;
   intermediate completed visits need interval coverage. Neither label
   equality nor static dominance antisymmetry supplies event ordering.
5. **Source PhiOcc:** its write footprint is the union of the leading PHIs'
   outputs. Unique definition identifies the member defining w. If destination
   is in the same block, di is a non-PHI after the leading prefix, so the
   body traversal crosses it after that batch. For a distinct destination,
   start the suffix path at this PhiOcc's label and use the separator. No
   incoming operand is evaluated in the post-PHI state by this argument.

Disposition: graph separator is checked; existing exports provide whole-prefix
coverage and actual fetch, but no audited export provides interval crossing
with the above conclusion. The required next repair is suffix path plus
interval instruction traversal (or a direct proof of this crossing interface)
before source-epoch stability, recursive chain validity, or wrapper migration.
No source-validity theorem, readiness change, or frozen-theorem edit is made.

## Checked strict temporal source stability (.53)

`loadElimTemporalStabilityTheory` builds without admissions (2026-11-09,
TO_load-elim-correct2-20261109T010004Z_m5823_t001). Its exports are:

- `le_occ_assign_crossing`: for an available destination `v` of static unary
  `v = ASSIGN w`, any selected source-writing occurrence forces a `v` writer
  strictly in its suffix. Both StepOcc and atomic PhiOcc sources are covered.
  Premises include actual entry-rooted occurrence prefix, wf_function,
  fn_inst_wf, wf_ssa, and destination availability at the endpoint.
- `le_occ_assign_source_no_write`: after a selected successful ASSIGN occurrence,
  if no suffix event writes its destination and that destination is available
  at the actual non-PHI endpoint, no suffix event writes its source variable.
- `le_occ_assign_source_lookup`: under exactly those premises,
  `lookup_var w s = lookup_var w t`, where `t` is the selected ASSIGN's post-state.
  This uses the existing occurrence suffix lookup theorem; no assumption of
  sequential execution within a PHI batch is made.

These are temporal interfaces only. They do not assert the ASSIGN value
relation, recursive chain validity, rebuilt global DFG soundness, or discharge
round readiness. The full-step semantic inversion and recursive reached-use
integration remain separate obligations.

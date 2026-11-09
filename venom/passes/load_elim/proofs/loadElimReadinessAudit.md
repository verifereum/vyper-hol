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
| aliases = ma_analyze b source addr_space (75) | B: memory_alias_analyze_def, mk_load_context_def | C: A_T vs ma_analyze b f1 Transient; A_S vs ma_analyze b f2 Storage; A_M vs ma_analyze b f3 Data and vs ma_analyze b f4 Calldata. Last two also change address space, not just function! |
| entry label = SOME s.current_bb (76) | B: frozen premise | C: entry preservation (structural, no execution theorem needed) |
| load analysis fixpoint (77-80) | A/B: le_load_analyze_fixpoint + le_solver_process_def, using wf_function f0 | A/B conditional on wf_function fi; fixpoint theorem itself works for any ctx, no alias equality needed |
| dfg_assigns_sound rebuilt DFG s (81) | B: frozen premise | C: new ASSIGN chains and PHI definitions change DFG; original DFG soundness is not this fact |
| bp_ptr_sound b s (82) | B: frozen premise | B: exactly same b and s |
| alloca_inv s (82) | B: frozen premise | B: exactly same s |
| allocas_in_word s (82) | B: frozen premise | B: exactly same s |
| bp_ptrs_bounded b source s (83) | B: frozen premise | B: unfold bp_ptrs_bounded_def using empty bp queries; source dependence then vacuous |
| le_step_preserves b rebuilt_DFG source (84) | B: unfold le_step_preserves_def and le_step_invariants_def; precisely frozen universal-step premise | C: universal premise ranges over new PHI/ASSIGN/NOP instructions and rebuilt DFG; original premise covers only original instructions and original DFG |
| successful PHIs preserve rebuilt DFG (85-89) | B: precisely frozen PHI premise | C: augmented batches and rebuilt DFG; original premise does not quantify over these |
| prefix freshness of fn_all_vars (90) | B: frozen premise | C: NOT a preservation invariant: a successful inserting round introduces variables with this prefix |
| no MEMTOP in source (91) | B: EVERY_MEM + frozen premise | C: simple structural opcode preservation needed; replacements add only ASSIGN/NOP/PHI, but no checked per-round wrapper located |
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

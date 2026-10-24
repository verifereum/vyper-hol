# Internal-function frames (#545)

## Implementation

Internal runtime and constructor bodies now set `ce_alloca_locals` before compiling
statements. This uses #652's **declaration-site** `declare_local` followed by
`emit_local_alloca`; it does not restore the old `reserve_local_ptrs` prototype.

Checked first-fit accepts individually valid overlapping occupied intervals.
New dead allocations still avoid every occupied interval. The
`checked_first_fit_SOME` conclusion now guarantees the new interval's validity and
its disjointness from each occupied interval, not disjointness among old intervals.

Concretized functions record transitive `(allocation, position, size)` metadata.
Callee identities enter caller liveness in sorted-set order; stored metadata keeps
its original order and diamonds deduplicate by identity. Imported allocations
participate in allocation conflicts, dead-allocation fill and eom. Only the neutral
`(0,0)` imported interval is omitted from physical occupancy; its identity remains
in metadata. The former whole-frame `call_frame_at_addr` and
`call_frame_reservations` definitions are removed.

A separate ordered-liveness replay supplies stable equal-livecount allocation
priority. Canonical finite-map livesets remain authoritative for membership.
Completion keeps the first occurrence of each present local key, preserving replay
priority when deterministic local-instruction fallback keys are appended. The proved
interface establishes distinctness, exact local membership,
canonical lookup consistency and local coverage. This is **not** a general proof
of equality with Python iteration over arbitrary multi-pointer may-sets.

Cleanup uses caller height, cycle-sensitive regional growth and a path-carried
promise, including invokes. Compatibility `generate_fn_plan*` interfaces remain;
context generation uses the cleanup-aware entry points. Simulation contracts are
unchanged. The interpreter uses main's external-call frame-preservation proof
without changes.

## New definition inventory

All names below are new relative to main `63fd7794`; `_def` suffixes omitted.

* `venomInst`: `allocation` datatype moved here from `memLocDefs`, and
  `ir_function.fn_mems_used` added. `mk_raw_function` initializes it to `[]`.
* `stackPlanTypes`: `ps_cleanup_height`, `ps_cleanup_growth`,
  `ps_cleanup_promised` fields; initialized to `NONE`, `[]`, `F`.
* `stackPlanGen`: `cleanup_frame_growth`, `cleanup_caller_height`,
  `cleanup_inst_transient`, `cleanup_block_summary`, `cleanup_reach_iter`,
  `cleanup_reach`, `cleanup_peel`, `cleanup_cyclic`, `cleanup_region_growth`,
  `cleanup_growth_table`, `cleanup_height_safe`, `init_cleanup_plan_state`,
  `generate_fn_plan_with_cleanup_analyzed`, `generate_fn_plan_with_cleanup`,
  `generate_fn_plan_with_cleanup_fuel`.
* `concretizeMemLocDefs`: `complete_alloc_positions_with_imports`,
  `callee_mems_used`, `unique_mems_used`, `imported_mems_used`,
  `context_alloca_size`, `context_mem_livesets`, `imported_liveset_info`,
  `apply_context_concretize_layout`, `ml_ordered_union`, `ml_ordered_inst`,
  `ml_ordered_insts`, `ml_ordered_block`, `ml_ordered_pass`, `ml_ordered_iter`,
  `ml_ordered_keys`, `ml_complete_order`, `alloc_liveset_items_ordered`.
* Concrete proof fixtures in `calleeMemoryWitness`: `witness_leaf`,
  `witness_arm`, `witness_ctx`, `witness_call`, `witness_zero`, `witness_ls`,
  `witness_one`, `witness_loop`.
* Concrete proof fixtures in `cleanupPromiseWitness`: `cleanup_probe_fn`,
  `cleanup_probe_live`, `cleanup_probe_state`, `cleanup_cycle_fn`.

Existing definitions changed include `compile_internal_function`,
`checked_first_fit`, allocation-map computation/context layout/application,
`cleanup_elision_safe`, `clean_stack_plan`, context plan generation,
`init_plan_state`, `mk_raw_function`, and `supported_function_body`.

## Oracle provenance and permanent coverage

`oracle/provenance.json` records the VYPER_PIN commit, settings, dependencies and
SHA256 source/output hashes. Settings match `python_o1_bytecode_oracle.py`:
experimental codegen, optimize NONE, Prague, no metadata. Python oracle bytes
were never replaced with HOL output. Asset refresh `40b48b02` preserved every
pre-existing JSON/hex byte-for-byte.

The permanent normative checked-frontend equalities cover:

* p01, p02, p03, p04, p06, p09, p10, p21, p39, p40, p41, p47, p74, p76, p92;
* `ctl_local_internal` and `nm_local_return_buf` in the name-collision group.

`evalCompilerInternalFrames` reaches the diamond and external-call child theories;
`vyperLoweringHol` now reaches it and already reaches `evalCompilerNameCollisions`.
No old full-parity rollup is needed for focused validation.

**Concrete expectation changes:** no existing pinned expectation changed. New
expectations are the 15 internal-frame and two name-collision pinned deploy/runtime
bytecode pairs above, plus the concrete allocation/cleanup witnesses in the two
proof-fixture theories. `ml_complete_order_priority_witness` additionally checks
first-occurrence priority with duplicate replay keys and a missing-local fallback.
It fails with last-occurrence deduplication. The #652 declaration witness checks
declaration *then*
emission, rather than expecting declaration alone to emit ALLOCA. Existing gas and
call-activation regression statements are unchanged; only their proofs were repaired.
`supported_internal_context_rejections` now retains its four internal-call cases;
the four local/loop cases move to `supported_internal_locals_and_loops` with
positive expectations, matching the removed internal-body shape guard. All eight
concrete cases remain covered.

## Reproducing focused checks

Build the permanent checked-frontend fixtures without the full parity rollup:

```text
holbuild build evalCompilerInternalFramesTheory evalCompilerNameCollisionsTheory
holbuild build staticLayoutAllocatorProofsTheory evalCompilerMemoryConstructionTheory
holbuild build cleanupPromiseWitnessTheory calleeMemoryWitnessTheory internalFrameWhitelistDiagnosticTheory
```

The fixture sources and `oracle/provenance.json` identify the programs and pinned
Python outputs. `vyperLoweringHol` also imports the three focused allocation,
cleanup and whitelist witness theories directly, so they are reachable from the
default lowering root without an opt-in parity rollup.

After the first-occurrence completion repair in `92e08d47`, a fresh seven-target
CI-mode build rebuilt `concretizeMemLocDefsTheory`, `staticLayoutAllocatorProofsTheory`,
`staticLayoutCompletionProofsTheory`, `concretizeMemLocTransitionProofsTheory`,
`evalCompilerMemoryConstructionTheory`, `evalCompilerInternalFramesTheory` and
`evalCompilerNameCollisionsTheory`. It exited 0 in 1059.648 seconds, saving all 11
memory-construction, 15 internal-frame and nine name-collision equalities, including
the previously failing `empty_dynarr_local_matches_python_oracle`.

A second focused build refreshed the finite 27-program control probe and the
39-function layout comparison; it exited 0 in 1576.884 seconds. Both builds used
`-j4 --skip-checkpoints --skip-proof-steps --no-cache --force=theory` at the unchanged
tactic budget. The 27 controls produced 21 MATCH, four bytecode residuals and two
NONE results; together with 13 other permanent cases, this is 34/40 MATCH. The
frame-size and P108 relocation results below were rechecked after the repair.
Baseline admissions remain in three `genBlockSim` theorems and `codegen_correct`; this work neither
introduces nor discharges those existing admissions. See [VALIDATION.md](VALIDATION.md)
for runtime frame sizes, residual diagnosis and behavioral provenance.

After merging main `639365c7`, CI-mode checking rebuilt `vyperInterpreterTheory`,
`evalCompilerMemoryConstructionTheory`, `evalCompilerInternalFramesTheory` and
`evalCompilerNameCollisionsTheory` with the same cache-disabling flags above and
`-j2`; it exited 0. All 11 memory-construction, 15 internal-frame and nine
name-collision oracle equalities were saved on that merged tree.

## Whitelist and statement changes

`supported_function_body` no longer requires `supported_internal_stmts_shape`.
The corresponding conclusion was removed from `supported_internal_body_contract`;
no new hypothesis was added. This statement change is additional to the first-fit
replacement described above. The internal-body and `For`-body
`expr_internal_call_root` exclusions remain because #546's necessary internal-call
ordering work is not present. Frame-layout tests alone do not justify removing
those exclusions.

## Observed behavior and validation limitations

* p39/p40 `foo(5)` were run through py-evm 0.12.1b1: both Python and HOL return 5;
  storage slot 0 is respectively 6 and 11. Permanent post-order byte equality also
  holds.
* Per-function runtime eom comparison covers 39 functions in 15 programs: 37
  equal, with only p58's internal and entry frames differing (see VALIDATION.md).
* Exact p108 source from public #546 was checked separately: its three runtime
  frames agree, and the 230-byte runtimes differ only in function placement and
  relocated jump destinations (#546); it is not counted as MATCH or in 34/40.
* Exact sources for p106, e01, e02 and p107 are not included in this fixture
  manifest; no permanent pinned equality for those names is claimed. The historical
  existing-MATCH controls p15, p16, p22, p27, p28, p29, p35, p37, p38, p59, p72,
  p75, p77, p78, p79, p81, p83, p84 and p91 likewise have not been rechecked here.
* Current-source diagnostics identify p57's call-result field offset (#558),
  p43b's extra Boolean-chain jump blocks (#556), and rc23/rc27/rc28's unimplemented
  `RawCallTarget` lowering (#554). rc23/rc27 fail the initial unit-wf guard;
  rc28 can compile to INVALID. These are not successful frame-layout regressions.
* p58 remains PARITY after the ordering repair. Pin-side pre-allocation IR has
  four 64-byte allocations, including the memory-resident concat offset; HOL has
  three and carries the offset in SSA (#566). This also changes the frame sizes.
  Equality of allocation ordering on these different input IRs is not claimed.
* p05's fresh control result is MATCH. Historical issue classifications do not
  establish current byte equality.
* p02/p47 now have permanent MATCH proofs, rather than residuals attributed to
  the closed #549.
* Validation is focused: neither a full-project build nor
  `evalCompilerBytecodeParityTheory` was run.

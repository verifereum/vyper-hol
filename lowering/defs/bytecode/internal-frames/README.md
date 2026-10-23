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
Completion enumerates present local keys once, with deterministic local-instruction
fallback. The proved interface establishes distinctness, exact local membership,
canonical lookup consistency and local coverage. This is **not** a general proof
of equality with Python iteration over arbitrary multi-pointer may-sets.

Cleanup uses caller height, cycle-sensitive regional growth and a path-carried
promise, including invokes. Compatibility `generate_fn_plan*` interfaces remain;
context generation uses the cleanup-aware entry points. Simulation contracts are
unchanged. A post-main-merge interpreter frame-preservation proof was repaired
compositionally; neither external-call semantics nor its statement changed.

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
proof-fixture theories. The #652 declaration witness checks declaration *then*
emission, rather than expecting declaration alone to emit ALLOCA. Existing gas and
call-activation regression statements are unchanged; only their proofs were repaired.

## Reproducing focused checks

Build the permanent checked-frontend fixtures without the full parity rollup:

```text
holbuild build evalCompilerInternalFramesTheory evalCompilerNameCollisionsTheory
holbuild build cleanupPromiseWitnessTheory calleeMemoryWitnessTheory internalFrameWhitelistDiagnosticTheory
```

The fixture sources and `oracle/provenance.json` identify the programs and pinned
Python outputs. `vyperLoweringHol` also imports the three focused allocation,
cleanup and whitelist witness theories directly, so they are reachable from the
default lowering root without an opt-in parity rollup.

Post-merge/order normal builds proved all 15 internal-frame and all nine
name-collision fixtures, including the four newly added equalities. The interpreter,
allocator, completion, transition and dispatcher dependencies also built locally.
A final focused `--skip-checkpoints --skip-proof-steps` check has not yet run.

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
* A per-function pinned-vs-HOL eom comparison is not yet reported.
* Exact sources for p106, e01, e02, p107 and p108 are not included in this fixture
  manifest; no permanent pinned equality for those names is claimed. The historical
  existing-MATCH controls p15, p16, p22, p27, p28, p29, p35, p37, p38, p59, p72,
  p75, p77, p78, p79, p81, p83, p84 and p91 likewise have not been rechecked here.
* Current-source diagnostics identify p57's call-result field offset (#558),
  p43b's extra Boolean-chain jump blocks (#556), and rc23/rc27/rc28's unimplemented
  `RawCallTarget` lowering (#554). rc23/rc27 fail the initial unit-wf guard;
  rc28 can compile to INVALID. These are not successful frame-layout regressions.
* p58 has an SSA-vs-memory concat-offset source difference (#566); an exclusive
  residual attribution after the ordering change has not yet been established.
  A fresh p05 control result is also pending. Historical issue classifications do
  not establish current byte equality.
* p02/p47 now have permanent MATCH proofs, rather than residuals attributed to
  the closed #549.
* Validation is focused: neither a full-project build nor
  `evalCompilerBytecodeParityTheory` was run.

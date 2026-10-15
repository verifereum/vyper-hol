# Compiler proof status — 2026-09-28 audit

This audit replaces [`archive/compiler-proof-status-2026-06-24.md`](archive/compiler-proof-status-2026-06-24.md).
It is a navigation and planning aid, not a proof artifact. The
[roadmap](compiler-proof-roadmap.md) describes what to do about the findings.

Audited revision: `main` at `5c9b1738` (after the Osaka and bytecode-parity
merges), built with `holbuild`.

## Method

1. **Source inventory.** Every live (uncommented) `cheat` in `*Script.sml`,
   attributed to its enclosing `Theorem` or `Resume`. There are 136 cheat
   sites in 112 theorem/resume entries across 40 files.
2. **Dependency closure.** Each theorem in the built `.holbuild/obj/**/*Theory.dat`
   files records its saved-theorem dependencies and oracle tags. From these,
   the audit computes which cheated theorems each top-level theorem transitively
   depends on, and which theorems depend on each cheat.
   Steps 1 and 2 are reproducible with
   [`tools/cheat_audit.py`](../tools/cheat_audit.py) (`sites`, `deps THY.THM`,
   `dependents`) after a `holbuild`.
3. **Statement review.** Every cheat was checked by reading its statement
   against the definitions the compiler actually executes, and against the
   hypotheses of the top-level theorem it would have to discharge.

## Headline findings

1. **The top theorem depends on exactly one cheat.**
   - `e2eCorrectness.vyper_call_correct` and its O1 instance
     `configuredE2ECorrectness.e2e_vyper_to_evm_O1` inherit the `cheat` tag
     only from `codegenCorrectness.codegen_correct`, which is a bare `cheat`.
   - Lowering, the Venom pipeline, codegen readiness, memory safety and the
     finalizer all enter as **hypotheses**.
2. **Most cheats are disconnected.** Of the cheated theorems in the build, only
   `codegen_correct` feeds the top theorem. Nearly all others have zero proved
   dependents; the few exceptions only feed their own pass's wrapper theorem.
   The proof is therefore a set of stage statements plus a composition proof,
   not a partially closed dependency tree.
3. **Several on-path statements are false as written.** These include
   `codegen_correct` itself, the lowering top theorem, and one e2e hypothesis
   (details below). The critical path therefore starts with **statement
   repair**, not proof search.
4. **Much of the remaining work is invisible in a cheat count.** Several O1
   passes have no correctness theorem at all. Others have theorems only about
   legacy variants the pipeline no longer runs. Nothing composes
   `run_venom_pipeline`. Deployment correctness is a `T` placeholder.
5. **Parity is in much better shape than in June.** The concrete compiler is
   `compile_vyper` with the pinned O1 schedule (`o1_pipeline_spec`,
   `venom/defs/venomPassScheduleScript.sml`). It reproduces pinned-Python
   deployment and runtime bytecode exactly for 101 fixtures (see
   [`bytecode-fixture-coverage.md`](bytecode-fixture-coverage.md)). The
   "minimal mandatory pipeline" the June roadmap asked for now exists; it is
   O1.

## Shape of the top-level theorem

`vyper_call_correct` (`lowering/e2eCorrectnessScript.sml`) is proved by
composition. Its hypotheses fall into three groups.

| Hypothesis | Class | Producer today | Notes |
|---|---|---|---|
| `lower_vyper_runtime_unit`, `compile_vyper_with`, `finalize_codegen`, `codegen_assembly` succeed | compiler run | — | Fine as is |
| `source_deployment_rel`, `call_state_rel`, `valid_vyper_call` | boundary / environment | caller | Fine as boundary facts |
| `source_unit_execution_correct tenv cenv am tx ret unit vs` | **lowering obligation** | none | Currently **false** for any program with `assert …, UNREACHABLE`: lowering emits `INVALID` (`ExHalt_abort`), but `external_call_result_rel` only accepts `Revert_abort` for `AssertException` |
| `checked_unit_transform_correct (run_venom_pipeline … o1_pipeline_spec) …` | **pipeline obligation** | none | No composition layer exists for `run_venom_pipeline` |
| `codegen_context_obligations Inv ctx cp` | mixed | partly | `codegen_ready`, `ctx_wf` and `reachable_fcg_acyclic` are checked at run time by `run_venom_pipeline`. `context_plan_layout_wf`, `entry_fn_no_ret` and `codegen_memory_obligations` have no producer |
| `codegen_reachability_package Inv ctx vs` | **lowering + pipeline invariant** | none | `Inv` is chosen by the caller |
| `initial_codegen_state_rel`, `initial_ctx_rel`, `ops_contain_at off …`, `asm_pc_to_offset prog off = 0` | **derivable** | none | Should follow from `call_state_rel` and the layout definitions |
| `finalizer_correct rpolicy finalizer` | finalizer | none | Unused by the proof. The theorem also assumes `runtime_bc = assemble prog`, so final assembly optimization is off the verified path |

Two further gaps sit in the e2e statement itself:

- **`rest` is unconstrained.** `rest` is quantified freely, so the conclusion
  talks about `run es` for nested frames. The codegen leg can only support
  that after the external-call and nested-context design is settled.
- **Deployment is a placeholder.** `e2e_deploy_correctness` concludes `T`.

## Cheat inventory by relevance

Classification key:

- **PATH**: the statement is right in spirit and is needed on the critical path.
- **RESTATE**: needed on the path, but the current statement is stale or false.
- **FALSE**: known false as stated and superseded; delete or rewrite rather
  than prove.
- **DEAD**: no users, and no role in the current architecture.
- **OPTIONAL**: true or plausible, but replaceable by something the pipeline
  already checks.
- **OFF**: only relevant to optional O2/O3/Os pipelines.

### Codegen leg (9 theorems, 20 sites)

| Cheat | Location | Class | Reason / action |
|---|---|---|---|
| `codegen_correct` | `venom/codegen/codegenCorrectnessScript.sml` | RESTATE | False: `initial_ctx_rel` lacks call/tx/block context, `vs_code`, `jumpDest` and `initial_codegen_state_rel`. It admits multi-frame `es` (STOP pops to the parent) and static contexts (Venom `SSTORE` ignores `cc_static`), and it needs gas sufficiency that no infrastructure supports |
| `codegen_fn_correct` | same | RESTATE | Same multi-context, static and gas problems. `Inv` is anchored at the entry function, but the statement is for any region `i` |
| `gen_fn_simulation` | `venom/codegen/venomToAsmPropsScript.sml` | RESTATE | Right shape (`context_venom_asm_rel`). `label_offsets`/`offset_to_pc` are not tied to `prog`, and there is no `IntRet` case, so it cannot be the INVOKE induction hypothesis |
| `gen_inst_simulation` | same | FALSE | Its own comment says it is false (PARAM). Superseded by `genBlockSim.gen_inst_ok_sim` |
| `gen_block_simulation` | same | FALSE / superseded | No label, PHI or entry invariants. Superseded by `blockSimHelpers.block_insts_sim` plus `gen_inst_*_sim` |
| `asm_bytecode_sim` | `venom/codegen/asmToBytecodePropsScript.sml` | FALSE | Superseded by the proved `asm_bytecode_sim_aux`, which is itself restricted to `no_asm_calls` and one context |
| `gen_inst_ok_sim` cases: `jmp`, `jnz`, `djmp` | `venom/codegen/proofs/genBlockSimScript.sml` | PATH | Need successor-transfer and PHI invariants |
| `gen_inst_ok_sim` cases: `assign_{live,dead}_{halt,nohalt}`, `log`, `assert_ok`, `assert_unreachable_ok` | same | PATH | Local cases; `assign_dead_halt` is nearly done |
| `gen_inst_ok_sim` case `some_name` | same | PATH (large) | Emit and postfix steps for every EVM-opcode instruction; only pure ops have emit lemmas |
| `gen_inst_halt_sim` INVOKE, `gen_inst_abort_sim` INVOKE | same | PATH | Need the function-level mutual induction hypothesis |
| `gen_inst_abort_sim` ASSERT | same | PATH | Needs cross-block `revert_postamble` label facts |

### O1 pipeline leg (12 theorems)

| Cheat | Location | Class | Reason / action |
|---|---|---|---|
| `simplify_cfg_fn_correct` | `venom/passes/simplify_cfg/proofs/simplifyCfgProofScript.sml` | PATH | About the dispatched function (`FST` of `simplify_cfg_fn_with_labels`). The conclusion is forward-only and needs termination equivalence for `pass_correct` |
| `cfg_norm_pass_correct` | `venom/passes/cfg_normalization/cfgNormCorrectnessScript.sml` | RESTATE | About legacy `cfg_norm_fn`; the pipeline runs `cfg_norm_function_supply` |
| `simplify_cfg_{establishes_all_reachable,preserves_ssa_form,preserves_wf_function}` | `venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml` | PATH (as needed) | Needed only as preconditions of later pass theorems. Final codegen readiness is checked at run time |
| `cfg_norm_{establishes_normalized_cfg,preserves_ssa_form,preserves_wf_function}` | `cfgNormCorrectnessScript.sml` | RESTATE / OPTIONAL | Legacy variant; last pass, so it only matters if a later proof consumes it |
| `sue_preserves_{ssa_form,wf_function}` | `venom/passes/single_use_expansion/singleUseExpansionCorrectnessScript.sml` | RESTATE | Legacy variant. Needed to feed DFT's `wf_ssa` precondition |
| `lower_dload_preserves_{ssa_form,wf_function}` | `venom/passes/lower_dload/lowerDloadCorrectnessScript.sml` | RESTATE | Legacy variant |

### Lowering and e2e leg (46 theorems)

| Cheat | Location | Class | Reason / action |
|---|---|---|---|
| `vyper_to_venom_correct` | `lowering/vyperLoweringCorrectScript.sml` | RESTATE | About `run_lowering_pair_compat`, which puts everything into a single function, so INVOKE targets do not exist. Inputs (`selectors`, `ext_fns`, `int_fns`, `cenv`, `tenv`) are not tied to `tops`, and there are almost no hypotheses on `vs`. Replace it with `lower_vyper_runtime_unit_correct`, concluding `source_unit_execution_correct` |
| `compile_expr_correct`, `compile_name_correct`, `compile_binop_correct`, `compile_neg_correct` | `lowering/exprLoweringPropsScript.sml` | RESTATE | `state_rel`/`vars_rel` only know `MemLoc` locals, but lowering now uses `PtrVar` + `ALLOCA`. `state_rel` lacks full accounts and transient-storage equality |
| `compile_expr_ci_mono` (backs `compile_expr_extends_insts`) | same | PATH | Plausible infrastructure |
| `compile_stmt_correct`, `compile_stmts_correct`, `compile_expr_stmt_correct`, `compile_annassign_correct`, `compile_if_correct`, `compile_for_range_correct`, `compile_assert_correct_true` | `lowering/stmtLoweringPropsScript.sml` | RESTATE | False once an expression does an INVOKE: they quantify `∀ctx`, use the single-function `assemble_function`, and cover only `INL ()` |
| `compile_assign_name_correct` | same | FALSE | Relates the pre-assignment state |
| `compile_assert_bare_correct_false`, `compile_assert_reason_correct_false` | same | RESTATE | Fine in shape; depend on the out-of-date expression lemma |
| `compile_return_{none,some}_internal_correct` | same | RESTATE | Assume a `MemLoc` `__return_pc__`; it is now `PtrVar` |
| `compile_return_{none,some}_external_correct` | same | RESTATE | Say nothing about returndata or state |
| `compile_abi_encode_to_buf_correct` (8 Resume cases) | `lowering/abiEncoderPropsScript.sml` | PATH (restate dynamic cases) | Needed for returndata = `enc`. The dynamic cases are forced into single-block `run_inst_seq` |
| `compile_abi_decode_static_correct` | same | RESTATE | Concludes only "OK or revert", nothing about the decoded value |
| `compile_abi_zero_pad_correct` | same | FALSE | No preconditions |
| `compile_raw_call_correct`, `compile_send_correct`, `compile_raw_create_correct`, `lower_abi_encode_correct`, `lower_abi_decode_correct` | `lowering/builtinPropsScript.sml` | RESTATE | Say only "does not Error"; no semantics |
| `compile_type_convert_correct` | `lowering/builtinTypeConvertPropsScript.sml` (not in rollup) | RESTATE | Building block only |
| `compile_selector_dispatch_linear_correct` | `lowering/moduleLoweringPropsScript.sml` | RESTATE | Must conclude that the exit label matches the calldata selector |
| `compile_generate_runtime_correct` | same | FALSE | Result shape only, and it misses `ExHalt` from `INVALID` |
| `compile_selector_dispatch_sparse_correct` | same | DEAD | O1 forces Linear dispatch (`lowering_policy_ok`) |
| `compile_entry_point_kwargs_correct` | same | DEAD | `compile_generate_runtime` never calls `compile_entry_point_kwargs` |
| `fresh_label_output_inj`, `compile_state_ok_{initial,emit_op,emit_void,emit_inst,fresh_var,fresh_id,new_block}`, `label_external_mono` | `lowering/emitHelperPropsScript.sml` | OPTIONAL | True for current definitions. Label distinctness can instead come from `unit_wf`, which `run_venom_pipeline` checks |
| `fresh_label_produces_external` | same | FALSE | Should conclude `label_external st' lbl`, not `st` |
| `lowering_memory_safe` | `lowering/proofs/loweringMemSafetyProofsScript.sml` (not in rollup) | RESTATE | Not needed for `source_unit_execution_correct`. It is the natural source of `alloca_safe_access` (ConcretizeMemLoc) and `codegen_memory_obligations`, but it is stated over the compat context and before the pipeline |
| `evm_correspondence_to_call_result` | `lowering/e2eCorrectnessScript.sml` | DEAD | `[local]`, no users |
| `o2_pipeline_ctx_pass_correct` | same | DEAD | `[local]`, no users; O2 is not the configured pipeline |

### Off the critical path (45 theorems)

These only matter for optional O2/O3/Os certification or have no users:

- **Pass cheats:** `algebraic_opt` (3), `assert_combiner` (2), `branch_opt` (2),
  `cse` (3), `dead_store_elim` (2), `function_inliner` (2),
  `internal_return_copy_fwd` (1), `load_elim` (4), `mem2var` (2),
  `memmerging` (1, not built), `memory_copy_elision` (11 theorems, 18 sites),
  `readonly_invoke_copy_fwd` (1), `remove_unused` (1), `revert_to_assert` (2),
  `tail_merge` (3).
- **Shared infrastructure:** `shared/proofs/copyFwdEquiv` (4; re-exported
  through `passSharedProps` but used by no O1 proof).
- **No users:** `venom/proofs/execEquivProofs.run_function_result_equiv_closed`.

## Hidden gaps (no cheat marks them)

### O1 pipeline

| O1 stage | Dispatched implementation | Semantic theorem status |
|---|---|---|
| DretDesugar | `dret_desugar_function` | **none** (structural facts only) |
| FmpLowering | `fmp_lower_function` | **none**; large (FMP calling convention) |
| Unreachable-function pruning | `prune_unit_fcg_unreachable` | **none**; needs "execution reaches only FCG-reachable functions" |
| MakeSSA (runs twice) | `make_ssa_current_fn` | Proved only for legacy `make_ssa_fn`, which requires PHI-free input; the second run has PHIs |
| LowerDload | `lower_dload_function_supply` | Proved only for the legacy function, under a vacuous `ld_no_mem_read` hypothesis. `ld_equiv` omits `vs_returndata`, so it does not imply `observable_equiv` |
| ConcretizeMemLoc | `apply_concretize_layout` | Core theorem proved, but it excludes INVOKE, LOG, MCOPY and external calls. Non-overlap is proved only for the legacy allocator. The `fn_eom` metadata change is not covered |
| SingleUseExpansion | `sue_expand_function_supply` | Proved only for legacy `sue_expand_function` |
| DFT | `dft_fn` (same function) | Proved, but assumes the unproved global `dft_schedule_safe`. Its abort relation `revert_equiv` does not imply `observable_equiv` |
| Label-map application | `apply_unit_label_map` | **none** |
| Composition | `run_venom_pipeline` | **none**. `venom_pipeline_correct` and friends are about the legacy uniform `venom_pipeline` |

### Other legs

- **Codegen:**
  - no function/context-level simulation for INVOKE/RET;
  - no gas-sufficiency infrastructure;
  - no bridge between the atomic Venom/asm call semantics and a pushed EVM frame;
  - asm→EVM step theorems require `no_asm_calls` and a single context.
- **Lowering:** the only facts produced today are syntactic
  (`run_lowering_integrity`, `run_lowering_static_integrity`,
  `run_lowering_global_reserved`), and no e2e theorem uses them.
- **Deployment:** `e2e_deploy_correctness` is `T`.

## Summary counts

| Group | Theorems with cheats | On the critical path (PATH + RESTATE) | FALSE / DEAD / OPTIONAL / OFF |
|---|---|---|---|
| Codegen | 9 | 6 | 3 |
| O1 pipeline | 12 | 12 | 0 |
| Lowering + e2e | 46 | 29 | 17 |
| Optional passes and unused infrastructure | 45 | 0 | 45 |

The codegen row counts the listed theorems (`gen_inst_ok_sim`, `gen_inst_halt_sim`
and `gen_inst_abort_sim` once each), not the 20 cheat sites.

The critical-path count is an upper bound on the *statements* to keep; it
says little about effort. The dominant costs are the hidden gaps above:
- pipeline composition and the missing pass theorems;
- function/context simulation, gas, and calls in codegen;
- the new alloca-aware lowering state relation.

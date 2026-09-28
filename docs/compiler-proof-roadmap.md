# Compiler correctness roadmap

This document is the plan for closing the end-to-end compiler correctness proof.
It is ordered by dependency, not calendar time. It was revised on 2026-09-28,
after the O1 pipeline, the bytecode-parity work and the Osaka migration landed.
The previous version is archived as
[`archive/compiler-proof-roadmap-2026-09-25.md`](archive/compiler-proof-roadmap-2026-09-25.md).

Related documents:

- [`compiler-proof-status.md`](compiler-proof-status.md): latest audit, with every cheat classified by relevance
- [`compiler-correctness-specification.md`](compiler-correctness-specification.md): theorem boundary and scope
- [`compiler-proof-dependencies.md`](compiler-proof-dependencies.md): cross-stage invariant structure
- [`compiler-definition-parity.md`](compiler-definition-parity.md): parity with `VYPER_PIN`
- [`bytecode-fixture-coverage.md`](bytecode-fixture-coverage.md): differential bytecode evidence
- [`compiler-proof-drafts-and-counterexamples.md`](compiler-proof-drafts-and-counterexamples.md): known false statements

## Where we are

**Settled since the previous roadmap:**

- **Target compiler.** `compile_vyper` with the pinned O1 schedule
  (`o1_pipeline_spec`), targeting `all_capabilities`. It is the concrete
  compiler whose output the theorem must cover.
- **Parity evidence.** 101 fixtures reproduce pinned-Python deployment and
  runtime bytecode exactly. The supported source subset is frozen and
  classified. This covers the practical content of the old Phase 0 (target
  and boundary) and Phase 1 (parity inventory) for the first theorem.
- **The minimal pipeline is O1.** It is no longer a separate thing to define.
- **Top theorem.** `vyper_call_correct` (and `e2e_vyper_to_evm_O1`) is proved
  as a composition. Its only cheat dependency is `codegen_correct`.
  Lowering, the pipeline, codegen readiness and memory obligations are
  hypotheses.

**Main problems (see the [status audit](compiler-proof-status.md)):**

1. **Some on-path statements are false.** This includes `codegen_correct`,
   `vyper_to_venom_correct` and one e2e hypothesis.
2. **Most stage theorems do not match the functions the compiler runs.** Pass
   theorems are about legacy variants, and lowering lemmas use a stale state
   relation and a single-function context.
3. **Nothing discharges the hypotheses.** No theorem produces the pipeline,
   memory or reachability hypotheses, and there is no composition layer for
   `run_venom_pipeline`.

## Principles

- **Repair statements before proving.** Do not spend effort on a cheat
  classified FALSE or RESTATE until its replacement statement is agreed. It
  must then be shown to compose with its consumer, for example by a short
  proof of the consumer from the new statement, left cheated.
- **Prove what the compiler runs.** Theorems about legacy pass variants,
  `run_lowering_pair_compat`, or the old `venom_pipeline` count only once
  they are bridged to the dispatched definition.
- **Let run-time checks do the work.** `run_venom_pipeline` already checks
  `unit_wf`, `codegen_ready` and `reachable_fcg_acyclic`. Use those checks
  instead of proving structural preservation, unless a later semantic proof
  needs the fact at an intermediate stage.
- **Close a vertical slice early.** Get a restricted fragment fully closed
  end to end before generalizing (see Milestone 2).
- **Keep the inventory honest.** Delete DEAD and FALSE cheats rather than
  leaving them as apparent progress. Record hidden gaps (missing theorems)
  next to cheats.

## Milestone 1: A true and complete top-level statement

Goal: every hypothesis of the top theorem is either a genuine boundary or
environment fact, or has a named producer theorem, even if that theorem is
cheated. Every cheat on the path should be believed true.

### 1.1 Codegen statement

Restate `codegen_correct` and `codegen_fn_correct`:

- Replace `initial_ctx_rel` with a relation that includes call, tx and block
  context, `vs_code`, `jumpDest = NONE` and `initial_codegen_state_rel`.
  Reuse `initial_state_rel`/`initial_state_bridge`, which are proved.
- Decide how to handle static contexts: either a hypothesis, or make Venom
  `SSTORE`/`TSTORE`/`LOG` semantics respect `cc_static`.
- Fix the call and nested-context design (spec section "Calls and nested
  contexts"). The recommended route is option 2: an atomic call relation,
  since Venom and asm calls are already atomic. That needs a bridge lemma
  between a fresh-state `run` and a pushed EVM frame, and it constrains
  `rest` in the e2e statement.
- State gas as an existential bound, as now, but plan the gas-sufficiency
  infrastructure it needs (Milestone 4.3).

Also restate `gen_fn_simulation`:

- tie `label_offsets` and `offset_to_pc` to `prog`;
- add the `IntRet` case so it can serve as the INVOKE induction hypothesis.

### 1.2 Lowering statement and the result relation

- Fix `external_call_result_rel`: an `AssertException` from `UNREACHABLE`
  corresponds to `Abort ExHalt_abort`. Without this, the lowering hypothesis
  is false for such programs.
- Replace `vyper_to_venom_correct` with `lower_vyper_runtime_unit_correct`.
  - **Hypotheses:**
    - `lower_vyper_runtime_unit tops rpolicy = SOME unit`;
    - a supported-program predicate matching the frozen parity subset;
    - `source_deployment_rel`, `valid_vyper_call`;
    - an initial Venom-state relation derived from `call_state_rel`.
  - **Conclusion:** `source_unit_execution_correct … unit vs`.

### 1.3 Pipeline statement

- Reconcile each pass's terminal/abort relation with `observable_equiv`.
  `ld_equiv` omits `vs_returndata`, and DFT's `revert_equiv` is too weak.
  Either strengthen the pass relations or change `ctx_transform_correct` so
  that aborts use a separate relation.
- State (cheated) a `run_venom_pipeline_correct` theorem for
  `o1_pipeline_spec` that produces `checked_unit_transform_correct`. It
  should also carry the lowering-to-codegen invariants (Milestone 5) through.

### 1.4 Derivable hypotheses

State the producer lemmas for:

- `initial_ctx_rel`/`initial_codegen_state_rel` from `call_state_rel`;
- `ops_contain_at off`, `asm_pc_to_offset prog off = 0`,
  `context_plan_layout_wf` and `entry_fn_no_ret` from the layout definitions.

These should be provable early.

Also:

- Drop `finalizer_correct` from the e2e statement (it is unused), or give it
  a meaning consistent with `runtime_bc = assemble prog`.
- Replace the `T` in `e2e_deploy_correctness` with a real statement (proof
  deferred to Milestone 6).

### 1.5 Inventory cleanup

- **Delete the DEAD cheats:**
  - `evm_correspondence_to_call_result`;
  - `o2_pipeline_ctx_pass_correct`;
  - `compile_selector_dispatch_sparse_correct`;
  - `compile_entry_point_kwargs_correct`;
  - `run_function_result_equiv_closed`, unless an O2 plan needs it.
- **Delete the superseded FALSE cheats:**
  - `gen_inst_simulation`;
  - `gen_block_simulation`;
  - `asm_bytecode_sim`.
- **Rewrite the local FALSE cheats:**
  - `fresh_label_produces_external`;
  - `compile_assign_name_correct`;
  - `compile_abi_zero_pad_correct`;
  - `compile_generate_runtime_correct`.
- **Leave the `compile_state_ok_*` family alone.** It is optional, since
  label distinctness comes from `unit_wf`. Keep it only if lowering proofs
  turn out to need it during compilation.

**Exit criterion:** the e2e theorem is re-proved from the restated stage
theorems. Every remaining cheat and hypothesis on the path is listed in the
status audit with a producer and a classification.

## Milestone 2: A closed vertical slice

Goal: the first cheat-free end-to-end theorem, restricted to a small fragment.
It validates that the Milestone 1 statements actually compose.

Suggested fragment:

- external functions only, with no internal calls (no INVOKE);
- no external calls or creates;
- static ABI arguments and returns;
- storage reads and writes, arithmetic, `if`, `assert`/`raise`;
- runtime only.

Fixtures such as `storage_read`, `storage_write`, `if_join` and
`assert_reason` are representative.

This slice avoids:

- the function-level INVOKE induction;
- the atomic-call bridge;
- dynamic ABI;
- the interprocedural parts of pipeline composition.

It still exercises every stage:

- the new lowering state relation;
- the per-function pass theorems;
- the label-map and pruning lemmas;
- block simulation, including the local `genBlockSim` cases;
- asm→EVM with gas.

State the fragment as a predicate on `tops`, not on the compiled output, so
the theorem remains a source-level claim.

## Milestone 3: Pipeline leg (O1)

Work items, roughly in dependency order.

1. **Composition layer.** Prove `run_venom_pipeline_correct` from per-stage
   theorems. This requires:
   - per-function replacement preserving `run_context`, with an
     interprocedural induction hypothesis over INVOKE for callee-first mixed
     contexts;
   - semantic preservation by `apply_unit_label_map`;
   - lifting from `run_function` to `run_context`;
   - termination equivalence for `pass_correct`;
   - chaining of the structural preconditions between passes.
2. **Bridge or re-prove on the dispatched variants:**
   - SingleUseExpansion (`sue_expand_function_supply`);
   - CFGNormalization (`cfg_norm_function_supply`; this also closes
     `cfg_norm_pass_correct`);
   - LowerDload (`lower_dload_function_supply`, without the vacuous
     `ld_no_mem_read`);
   - MakeSSA (`make_ssa_current_fn`, including PHI-containing input for its
     second run).
3. **Prove the open semantic cheat.** `simplify_cfg_fn_correct` is already
   about the dispatched function.
4. **Missing theorems:**
   - DretDesugar;
   - unreachable-function pruning ("execution reaches only FCG-reachable
     functions");
   - FmpLowering (large).
5. **DFT.** Prove `dft_schedule_safe`, or restate DFT correctness so that it
   does not need that global property.
6. **ConcretizeMemLoc:**
   - extend coverage to INVOKE, LOG, MCOPY and external calls;
   - prove non-overlap for the `compute_function_layout_*` allocator the
     pipeline uses;
   - cover the `fn_eom` metadata update.
7. **Structural cheats.** Keep the SimplifyCFG, SUE and LowerDload
   `ssa`/`wf` cheats only where a later pass theorem consumes them. Restate
   them on the dispatched variants.

## Milestone 4: Codegen leg

1. **Local block cases in `genBlockSim`:**
   - `jmp`/`jnz`/`djmp`, using successor-transfer and PHI invariants;
   - the four `assign` cases;
   - `log`, `assert_ok`, `assert_unreachable_ok`;
   - ASSERT abort, using `revert_postamble` label facts;
   - `some_name`: emit lemmas for every EVM-opcode instruction. This is the
     largest local item.
2. **Function and context simulation.** Prove the restated
   `gen_fn_simulation` by mutual fuel induction covering INVOKE/RET frames,
   return-label tokens and per-frame plan states. This closes the INVOKE
   cases of `gen_inst_halt_sim`/`gen_inst_abort_sim`. `fnPlanDecomp`
   provides the structural decomposition.
3. **asm→EVM:**
   - gas-sufficiency infrastructure (none exists yet);
   - the atomic external-call bridge from Milestone 1.1;
   - lifting the `no_asm_calls` and single-context restrictions of
     `asm_evm_step`/`asm_bytecode_sim_aux`.
4. **`codegen_correct`**, from the pieces above and the proved
   `initial_state_bridge`, `block_insts_sim` and `terminal_asm_evm_final`.

## Milestone 5: Cross-stage invariants

This milestone produces the hypotheses that currently have no producer.

- **Lowering memory invariant.** Restate `lowering_memory_safe` over the
  packaged `run_lowering` output rather than the compat context. The
  invariant must imply ConcretizeMemLoc's `alloca_safe_access`.
- **Preservation through O1.** Carry the invariant through SimplifyCFG,
  DretDesugar, MakeSSA and LowerDload, which run before ConcretizeMemLoc. Then
  prove `codegen_memory_obligations` on the pipeline output.
- **Reachability.** Pick `Inv` for `codegen_reachability_package`, prove it
  from lowering, and preserve it through the pipeline.

## Milestone 6: Lowering leg

1. **State relation.** Define an alloca-aware `vars_rel`: a `PtrVar` pointer
   maps to a `vs_allocas` region holding `val_in_memory`. It should be part
   of a `state_rel` with full accounts and transient-storage equality and a
   `PtrVar` `__return_pc__`.
2. **Expressions.** Restate the expression lemmas over `run_blocks` in
   `unit.cu_context`, INVOKE-aware, and then prove them: name, binop, neg and
   the others needed by the supported subset. `compile_expr_ci_mono` is
   infrastructure.
3. **Statements.** Cover statements and statement lists, including the
   return/Halt/Revert/ExHalt outcomes, and internal returns through the
   `IntRet` lemma.
4. **ABI:**
   - `compile_abi_encode_to_buf_correct`, with multi-block dynamic cases;
   - static decode, restated to describe the decoded value;
   - external return: returndata = `enc …`.
5. **Module:**
   - linear dispatch reaches the entry for the calldata selector;
   - argument decoding establishes `vars_rel`;
   - `lower_vyper_runtime_unit_correct`.
6. **Builtins.** Only those in the supported subset, driven by fixtures:
   `send`, `raw_call` and `raw_create` depend on the atomic-call design;
   `compile_type_convert_correct` should be wired into the rollup once it is
   restated.
7. **Deployment.** Constructor lowering, runtime-bytecode embedding,
   immutables and deployed-code return. Together with Milestone 4, this
   closes the restated `e2e_deploy_correctness`.

## Milestone 7: Full theorem

- Discharge all e2e hypotheses except the boundary and environment ones, for
  the full supported subset.
- Runtime and deployment theorems.
- Nested and multi-contract corollaries under the chosen call relation.

## Deferred

These do not block the first end-to-end theorem.

- **Optional pipelines.** O2/O3/Os certification, and the 45 cheats in
  optimization passes and unused shared infrastructure listed as "off the
  critical path" in the status audit.
- **Final assembly optimization.** The e2e theorem assumes
  `runtime_bc = assemble prog`. Any change here should go with a concrete
  finalizer theorem.
- **Frontend.** Parsing, JSON import and type checking remain trusted
  boundary inputs (see the specification).

## Parallel tracks

After Milestone 1, the work splits cleanly:

| Track | Scope | Shared interface |
|---|---|---|
| A: Lowering | Milestone 6 | `state_rel`, `lower_vyper_runtime_unit_correct` statement |
| B: Pipeline | Milestone 3 | per-pass relation vs `observable_equiv`; `run_venom_pipeline_correct` statement |
| C: Block codegen | Milestone 4.1 | `gen_inst_*_sim` statements (stable) |
| D: Function codegen and asm→EVM | Milestone 4.2–4.4 | restated `codegen_correct`, call relation |
| E: Invariants | Milestone 5 | memory and reachability invariant definitions |

Milestone 2, the vertical slice, should draw on every track before any track
generalizes to the full subset.

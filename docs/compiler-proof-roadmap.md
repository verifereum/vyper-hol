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
- **Calls to other contracts** (decided 2026-09-29, following #98). The
  theorem covers one call into the contract, and a call to another contract
  is one step on both the source and the compiled side. See 1.1.
- **`finalizer_correct` is dropped** (decided 2026-09-29). The e2e
  statement fixes the finalizer to the identity. See 1.5.

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
- **Close restricted results early.** First close one stage for a
  restricted class of programs, then a whole path from source to bytecode,
  before generalizing (see Milestone 2).
- **Keep the inventory honest.** Delete DEAD and FALSE cheats rather than
  leaving them as apparent progress. Record hidden gaps (missing theorems)
  next to cheats.

## Milestone 1: A true and complete top-level statement

Goal: every hypothesis of the top theorem is either a genuine boundary or
environment fact, or has a named producer theorem, even if that theorem is
cheated. Every cheat on the path should be believed true.

### 1.1 Call boundary, external calls and gas

This section records how the proof treats a call from compiled code to
another contract (decided 2026-09-29, following the discussion on
[#98](https://github.com/verifereum/vyper-hol/issues/98)). The spec section
"Calls and nested contexts" gives the summary. This section has the details
and the work it creates.

Terms used below:

- A **call frame** is one EVM execution context: the code being run, its
  stack, memory and program counter. A contract call pushes a new frame onto
  Verifereum's context list (`es.contexts`), and returning pops it.
- Verifereum's **`run`** executes until the whole context list is finished.
  Its **`run_call`** (`vfmExecution`) executes only until the current frame
  returns to its caller.
- A call is **atomic** in a proof when the whole callee execution, including
  every call it makes in turn, is treated as a single step.

**What the top theorem is about.**

- It covers one call into the compiled contract: the frame on top of
  `es.contexts = (ctxt, rb) :: rest`. The caller frames `rest` can be
  anything, so the call can be the top-level transaction or come from
  another contract.
- The conclusion is stated with `run_call es = SOME (r, es')`, not `run`.
  It relates the source result to:
  - `r` and the returndata;
  - logs, accounts and transient storage;
  - what the caller sees after the frame is popped.
- Today `rest` is unconstrained, but the conclusion uses `run`, which also
  runs the callers after our frame returns. The new statement fixes this.
  The top-level transaction case (`rest = []`) follows from Verifereum's
  `run_call_eq_run_single_context`, which says `run_call` and `run` agree
  when there is only one frame.
- Replace `vyper_evm_correspondence`, which uses `run`, with this
  `run_call` relation. `e2eCorrectnessScript.sml` has its own copy of
  `run_call_def`; delete it and use Verifereum's definition. Also delete the
  cheated `evm_correspondence_to_call_result` (1.6). Verifereum already
  proves facts about `run_call` that the proof can reuse, for example:
  - `run_call_inl_length`;
  - `run_within_frame_preserves`;
  - `same_frame_rel`;
  - the `run_call_preserves_*` theorems.

**Calls to other contracts are atomic on both sides.**

- In the source semantics, an external call runs the callee with
  Verifereum. That includes everything the callee does, even calls back
  into our contract. The source semantics only interprets the Vyper code of
  the outer call.
- In the compiled code, a `CALL`, `STATICCALL` or `CREATE` instruction
  likewise starts a Verifereum execution of the callee. The asm→EVM proof
  treats that execution as one step of our frame.
- The theorem therefore does not assume anything about the callee's code,
  including our own contract's code if the callee calls back into it. To
  reason about such a call back, apply the theorem again at the state where
  that inner call starts (Milestone 7).

**The two sides do not yet run the callee the same way.** The source
semantics builds the callee's starting state with `make_ext_call_state`.
That state is a fresh transaction containing only the callee frame. The
compiled `CALL` instead pushes the callee frame on top of the real ones.
They differ in:

- **Gas.** The source gives the callee `default_call_gas_limit = 2 ** 64`.
  The EVM gives it at most the caller's remaining gas (at most 63/64 of it,
  EIP-150).
- **Warm addresses.** The EVM charges less for addresses and storage slots
  already used in the transaction. The source resets that set to
  `{caller, callee}`.
- **Call depth.** The EVM fails calls nested more than 1024 deep. The
  source callee always starts at depth 1.
- **Other transaction state:** the list of accounts to delete at the end
  of the transaction (`toDelete`), and `msdomain`.

Either make the source call start from the same state as the compiled
call, or list these differences as assumptions of the lemma relating the
two. Gas matters most: a callee that runs out of gas on the EVM succeeds in
the source, where it has 2^64 gas.

**Gas values come from an oracle (#98).** Here, an *oracle* is a list of
numbers given to the source semantics from outside. The source takes the
next number whenever it needs a gas value it cannot compute itself: for
`msg.gas`, and for the gas passed to an external call.

- The oracle is not part of the contract state (`abstract_machine`). A
  revert does not give values back to it, and each new top-level call
  starts with a new list.
- The oracle holds only the gas values read by our frame. The callee's own
  gas reads are not in it.
- The theorem requires the oracle to agree with the compiled frame's
  execution. Each compiled `GAS` instruction must return the next oracle
  value. A compiled external call, treated as one step, uses no oracle
  values beyond the one for the gas it passes.
- The oracle cannot be chosen independently of the compiled run. The gas a
  compiled `CALL` passes on depends on how much gas the compiled code has
  used so far. So the theorem statement must read the oracle values off
  the compiled `run_call` execution.

Open points for the statement:

- What each gas value means exactly:
  - `msg.gas`: the result of the `GAS` instruction, after `GAS` itself is
    charged;
  - gas for a call without `gas=`: the gas the caller has left, the gas
    requested, the gas after the 63/64 cap, or the callee's actual limit;
  - explicit `gas=`: the frontend currently ignores it;
  - creates, precompiles and out-of-gas.
- `msg.gas` (`MsgGas`) is outside the supported source subset: no fixture
  uses it. External calls are inside it. So the call-gas value is needed
  for the first theorem, and `msg.gas` is not.
- Verifereum may lack a theorem that splits a full execution into three
  parts: up to the start of a nested call, `run_call` for that call, and
  the rest after it returns. Only Milestone 7's corollaries need it.
  Confirm the exact statement before asking the Verifereum maintainers.

### 1.2 Codegen statement

Restate `codegen_correct` and `codegen_fn_correct`:

- Replace `initial_ctx_rel` with a relation that includes call, tx and block
  context, `vs_code`, `jumpDest = NONE` and `initial_codegen_state_rel`.
  Reuse `initial_state_rel`/`initial_state_bridge`, which are proved.
- Decide how to handle static contexts: either a hypothesis, or make Venom
  `SSTORE`/`TSTORE`/`LOG` semantics respect `cc_static`.
- Conclude over `run_call` for the entered frame (1.1). The current
  statement also admits multi-frame `es`, where `STOP` pops to the parent.
- Keep the gas assumption on our own frame as it is now: there is some
  amount of gas that is enough. The gas passed to a callee comes from the
  gas oracle (1.1). Plan the infrastructure for proving that a gas amount
  is enough (Milestone 4.3); none exists yet.

Also restate `gen_fn_simulation`:

- tie `label_offsets` and `offset_to_pc` to `prog`;
- add the `IntRet` case so it can serve as the INVOKE induction hypothesis.

### 1.3 Lowering statement and the result relation

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

### 1.4 Pipeline statement

- Reconcile each pass's terminal/abort relation with `observable_equiv`.
  `ld_equiv` omits `vs_returndata`, and DFT's `revert_equiv` is too weak.
  Either strengthen the pass relations or change `ctx_transform_correct` so
  that aborts use a separate relation.
- State (cheated) a `run_venom_pipeline_correct` theorem for
  `o1_pipeline_spec` that produces `checked_unit_transform_correct`. It
  should also carry the lowering-to-codegen invariants (Milestone 5) through.

### 1.5 Derivable hypotheses

State the producer lemmas for:

- `initial_ctx_rel`/`initial_codegen_state_rel` from `call_state_rel`;
- `ops_contain_at off`, `asm_pc_to_offset prog off = 0`,
  `context_plan_layout_wf` and `entry_fn_no_ret` from the layout definitions.

These should be provable early.

Also:

- **Decision (2026-09-29): drop `finalizer_correct`** from the e2e
  statement and its definition from `e2eDefsScript.sml`. Reasons:
  - The proof does not use it.
  - The finalizer is the step that may rewrite the generated assembly
    before it is assembled into bytecode. Under O1 the final-assembly policy
    is always `FAP_Optimize`. With that policy, `finalizer_correct` only
    says the finalizer's output is target-safe, and `finalize_codegen`
    already checks that.
  - It says nothing about whether the finalizer preserves behaviour, so it
    could not support a finalizer that actually changes the assembly.

  Instead, fix the finalizer to the identity `K SOME`, which the fixtures
  already use. Then prove `runtime_bc = assemble prog` from
  `finalize_codegen_identity` instead of assuming it.
- Replace the `T` in `e2e_deploy_correctness` with a real statement (proof
  deferred to Milestone 6).

### 1.6 Inventory cleanup

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

## Milestone 2: First closed results

Goal: theorems with no cheats as early as possible, for restricted classes of
programs, before any stage is generalized. There are two steps. 2.1 is
small and closes one stage. 2.2 then closes a whole path from source to
bytecode.

### 2.1 First closed stage: codegen for one function without calls

Prove the restated `codegen_correct` (1.2), with no cheats, for Venom
contexts that satisfy all of the following:

- **One function, no `INVOKE`.** `INVOKE` is the Venom instruction that
  calls another Venom function. Lowering emits it only for a call to an
  internal Vyper function (`compile_call`, `exprLoweringScript.sml`).
  External function bodies are compiled into the single entry function, and
  O1 removes functions that nothing calls (`ps_prune_unreachable`). So any
  source program without internal calls compiles to a context of this kind.
- **No calls to other contracts:** no `CALL`, `STATICCALL`,
  `DELEGATECALL` or `CREATE`.
- **No `GAS` instruction.** This keeps gas values out of the program's
  results.
- **Only opcodes whose emission lemmas are proved.** An *emission lemma*
  says that the assembly generated for one Venom instruction does what the
  instruction does. Start from the opcodes that the fixtures `storage_read`,
  `storage_write`, `if_join` and `assert_reason` use, and grow the list.

State the class as a predicate on the Venom context. This is a stage
theorem, and the Venom context is its input.

**Why this step first.** It is small, and it also carries the most risk,
because it is the first place the proof meets the real EVM:

- **Gas.** The theorem says that some amount of gas is enough. That needs
  a new argument: in this class of programs, EVM execution with more gas
  gives the same result, apart from running out. Nothing for this exists
  yet. Check first what Verifereum already proves about gas.
- **Layout.** It exercises the stack layout, memory layout and jump
  destinations that codegen produces.
- **Statement.** It tests the restated `codegen_correct` statement, the
  `run_call`-based result relation (1.1) and the derivable hypotheses
  (1.5).

It does not need:

- the function-level induction over `INVOKE` (4.2);
- the call lemma or the gas oracle (1.1);
- any work on lowering or the pipeline.

**Work:**

- the remaining single-instruction cases of `gen_inst_ok_sim` in
  `genBlockSim`: jumps (`jmp`/`jnz`/`djmp`), the `assign` cases, `log`,
  and the two `assert` cases;
- the `ASSERT` failure case of `gen_inst_abort_sim`;
- emission lemmas for the opcodes in the class;
- the gas argument above;
- lifting `asm_evm_step`/`asm_bytecode_sim_aux` from "exactly one frame"
  to "our frame, with any caller frames below it". For a frame that makes
  no calls, this should follow from Verifereum's `run_within_frame`
  results. If it turns out to be costly, first prove the case with no
  caller frames.

**Smaller first task.** Close the single-instruction cases of
`gen_inst_ok_sim` other than `INVOKE`. It closes no theorem by itself, but
it can start before the restated statements of Milestone 1 are agreed.

**Afterwards,** codegen grows in two steps (Milestone 4): add `INVOKE`
(4.2), then calls to other contracts and `GAS` (4.3), which completes
`codegen_correct`.

### 2.2 A closed path from source to bytecode

Goal: the first end-to-end theorem with no cheats, for a small class of
source programs. It checks that the statements from Milestone 1 compose
across all stages. It builds on 2.1 for the codegen part.

Suggested class of programs:

- external functions only, with no internal calls (so no `INVOKE`, as in
  2.1);
- no calls to other contracts and no contract creation;
- ABI arguments and return values of fixed size only;
- storage reads and writes, arithmetic, `if`, `assert`/`raise`;
- runtime code only, no deployment.

Fixtures such as `storage_read`, `storage_write`, `if_join` and
`assert_reason` are representative.

This class avoids:

- the function-level `INVOKE` induction;
- the lemma relating a source external call to a compiled one (1.1);
- ABI values of variable size;
- the parts of pipeline composition that involve more than one function.

It still exercises every stage:

- the new lowering state relation;
- the per-function pass theorems;
- the label-map and pruning lemmas;
- codegen, from 2.1.

State the class as a predicate on `tops`, the source program, not on the
compiled output, so the theorem remains a claim about source programs.

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
   - the lemma from Milestone 1.1 relating calls: a compiled `CALL` or
     `CREATE`, together with the whole callee execution it starts, has the
     same result as the source external call, and uses one gas-oracle value;
   - each compiled `GAS` instruction returns the next gas-oracle value;
   - lifting the restrictions of `asm_evm_step`/`asm_bytecode_sim_aux`,
     which currently allow no calls (`no_asm_calls`) and only one frame.
     They should instead hold for our frame with any caller frames below
     it, using Verifereum's `run_within_frame` results.
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
   `send`, `raw_call` and `raw_create` need the call lemma and the gas
   oracle from 1.1;
   `compile_type_convert_correct` should be wired into the rollup once it is
   restated.
7. **Deployment.** Constructor lowering, runtime-bytecode embedding,
   immutables and deployed-code return. Together with Milestone 4, this
   closes the restated `e2e_deploy_correctness`.

## Milestone 7: Full theorem

- Discharge all e2e hypotheses except the boundary and environment ones, for
  the full supported subset.
- Runtime and deployment theorems.
- Nested, reentrant and multi-contract corollaries. Apply the frame theorem
  separately at each nested entry state (1.1). The decomposition of a full
  run around a nested frame may need to come from Verifereum.
- Multi-transaction composition, by induction over the persistent
  world-state relation, with a new gas oracle for each top-level call.

## Deferred

These do not block the first end-to-end theorem.

- **Optional pipelines.** O2/O3/Os certification, and the 45 cheats in
  optimization passes and unused shared infrastructure listed as "off the
  critical path" in the status audit.
- **Final assembly optimization.** The e2e theorem fixes the identity
  finalizer (1.5). A non-identity finalizer needs a semantic preservation
  theorem, which the dropped `finalizer_correct` never provided.
- **Frontend.** Parsing, JSON import and type checking remain trusted
  boundary inputs (see the specification).

## Parallel tracks

After Milestone 1, the work splits cleanly:

| Track | Scope | Shared interface |
|---|---|---|
| A: Lowering | Milestone 6 | `state_rel`, `lower_vyper_runtime_unit_correct` statement |
| B: Pipeline | Milestone 3 | per-pass relation vs `observable_equiv`; `run_venom_pipeline_correct` statement |
| C: Block codegen | Milestone 4.1 | `gen_inst_*_sim` statements (stable) |
| D: Function codegen and asm→EVM | Milestone 4.2–4.4 | restated `codegen_correct`, `run_call`-based result relation, gas oracle (1.1) |
| E: Invariants | Milestone 5 | memory and reachability invariant definitions |

Milestone 2.1 comes from track C and part of track D. Milestone 2.2
draws on every track, and should be closed before any track generalizes
to the full supported subset.

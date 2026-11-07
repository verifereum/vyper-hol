# TASK: S3: __entry reaches the external body start memory-safely (external_entry_reaches_body_mem)

## Meta
Status: planned
Priority: P1
Created: 2026-11-04; moved 2026-11-05
Location: project root (theorem in `lowering/loweringMemEntryReachScript.sml`, theory `loweringMemEntryReach`)

## Theorem Statement (FROZEN)

```sml
Theorem external_entry_reaches_body_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      stmt_state_rel unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      alloca_history func s0 /\
      ~s0.vs_halted /\ s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      cenv.ce_return_buf = NONE /\
      ((!fuel. mem_safe_run fuel unit.cu_context func s0) ==>
       !fuel. mem_safe_blocks fuel unit.cu_context efn
                (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                            vs_inst_idx := 0 |>))
```

It is currently proved by `cheat` in `lowering/loweringMemEntryReachScript.sml` (theory `loweringMemEntryReach`).
Replace that cheat with a real proof.

**Do not modify this statement, or any definition it uses.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THE MAIN PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Helper lemmas go in new theory files under lowering/,
 * imported by loweringMemEntryReach, each built before the
 * main proof.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build loweringMemEntryReachTheory` passes with zero failures, and `external_entry_reaches_body_mem` and every new helper have no CHEAT. Theories outside your helpers may still contain inherited admissions (other runs prove them); don't remove or add any cheat there.
2. No duplicate or near-duplicate lemmas: search the `.sig` files under `.holbuild` and `lowering/*.sml`, `venom/**/*.sml` before stating a new one, and reuse what exists.
3. No new axioms, no new premises on the frozen theorem, no changes to any definition (nothing under `lowering/defs/`, `semantics/`, `venom/` definitions, `lowering/bodyMemoryDefsScript.sml`, `lowering/bodySimScript.sml`, `lowering/stmtSimScript.sml` definitions).
4. Put new helper lemmas in new theory files under `lowering/` named for their content, e.g. `entryReachMemScript.sml`, imported by `loweringMemEntryReach` (add them to its `Ancestors`); register nothing else. Helpers that no other theory uses are `[local]`. Proofs stay under 50 lines each.
5. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout changes: every step must fit the default 2.5 s.
6. Commits: commit only `.sml` files under `lowering/` (and this TASK file at the project root); never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*` or tool output. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample (program, call, state), state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
cd <worktree root, the directory with holproject.toml>
holbuild -j4 build loweringMemEntryReachTheory
```

## Background

- What it says: when the call value is accepted, the run from `__entry` reaches the start `sa` of the selected external function's guarded body in a state `s0` that the body judgment can start from (`stmt_state_rel` in the body's compile env `cenv`, `alloca_history`, no caller return buffer), and a memory-safe run from `s0` makes the whole run from `__entry` memory-safe: the selector dispatch and entry checks touch no memory, and the argument decode (`compile_register_positional_args`: an ALLOCA per parameter, then its decode) writes only the parameters' own buffers.
- `func` is existential: in the lowered unit the external bodies are blocks of `__entry` itself (`compile_generate_runtime`; `extract_context_with_internals` splits off only internal functions), reached by `JMP`, so `func` = `efn` is the natural witness.
- Arguments: `supported_program` allows dynamic parameter types (`String[n]`, `Bytes[n]`, `DynArray`, and aggregates of them), not only static ones. The existing body-entry state relation `external_body_entry_state_rel` (`lowering/entryStateRelScript.sml`) and the memory leaf `entry_decode_arg_mem_ok` cover word and static-ABI arguments only; the dynamic decode (`compile_abi_decode_to_buf`, which has its own loops, scratch ALLOCAs and blocks) has S1-side correctness proofs in the `abiDecoder*` theories but no memory or entry-relation lemma yet. `external_body_entry_state_rel` also does not export `local_ptrs_reserved` or `stmt_state_rel`'s allocation parts (`alloca_inv`, `alloca_room`, the immutable separation).
- Memory safety: `mem_safe_run`, `mem_safe_blocks`, `mem_safe_block`, `mem_safe_step` (`venom/compiler/memSafeRunScript.sml`): every instruction executed reads and writes memory below the allocation frontier `vs_alloca_next` (`inst_mem_below_frontier`, `lowering/instMemFrontierScript.sml`), or is a revert forward (`inst_mem_ok_in_fn`, `unitTransformDefs`). `mem_safe_blocks` spends one fuel per block entered; `mem_safe_run_all_fuel`, `mem_safe_blocks_run`, `mem_safe_run_inst_seq` are the unfolding lemmas.
- The consumer is the body-run composition in `lowering/loweringMemBodyRunScript.sml` and `lowering/loweringMemCorrectScript.sml`: read them to see how the theorem is used.
- The theorem is the memory twin of S1's `external_entry_reaches_body` in `lowering/loweringRuntimeCorrectScript.sml`. That S1 lemma is itself still an admission (cheat) and gives no information about memory, so it is no shortcut; you may read its comment for intent.

## Domain Constraints

- Follow the lowering as defined; don't assume a supported subset narrower than `supported_program` gives.
- Stage lemmas stay generic: nothing here may fix the O1 finalizer or pass policy.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Memory-safe run defs and unfolding | `venom/compiler/memSafeRunScript.sml` | `mem_safe_run`, `mem_safe_blocks`, `mem_safe_blocks_run`, `mem_safe_run_all_fuel` |
| Per-opcode frontier facts | `lowering/instMemFrontierScript.sml` | `below_frontier_<OPC>`, `below_frontier_no_ranges` |
| Memory fragment judgment | `lowering/fragExecMemScript.sml` | `frag_exec_mem`, `run_inst_seq_mem_ok`, `frag_exec_mem_run_inst_seq`, `mem_safe_run_inst_seq`, `frag_exec_mem_assert_fail`, `frag_exec_mem_seq` |
| Allocation footprints | `lowering/allocaFootprintScript.sml`, `venom/proofs/allocaHistoryScript.sml` | ALLOCA at a site, `alloca_next_valid`, `alloca_history` and its step/jump lemmas |
| Entry/halt memory leaves (proved) | `lowering/entryHaltMemScript.sml`, `lowering/rawReturnMemScript.sml` | return none/STOP, word return, static copy return, raw return, static argument decode (`entry_decode_arg_mem_ok`) |
| Body memory judgments | `lowering/bodyMemoryDefsScript.sml` | `stmt_frag_mem`, `frame_ret_ok_mem`, `expr_sim_mem`, `return_buf_frame` |
| S1 fragment framework | `lowering/fragExecScript.sml`, `lowering/stmtSimScript.sml`, `lowering/bodySimScript.sml` | `frag_exec`, `stmt_frag`, `stmt_state_rel`, `stmt_exit`, `exit_result` |
| The lowering | `lowering/defs/moduleLoweringScript.sml`, `lowering/defs/stmtLoweringScript.sml`, `lowering/defs/abiEncoderScript.sml`, `lowering/defs/vyperCompilerScript.sml`, `lowering/compileVyperScript.sml` | `compile_generate_runtime`, `compile_external_fn_bodies`, `compile_entry_checks`, `compile_register_positional_args`, `compile_guarded_body`, `compile_external_return`, `compile_abi_encode_to_buf`, `compile_abi_decode_to_buf`, `run_lowering`, `extract_context_with_internals` |
| Supported subset | `lowering/supported/` | `supported_program`, `supported_place_type` |
| Vyper reference at VYPER_PIN | `alan-ref/vyper/vyper/codegen_venom/` | the Python lowering the HOL lowering follows |
| Body-start state relation (static args) | `lowering/entryStateRelScript.sml`, `lowering/entryArgPtrsScript.sml`, `lowering/entryLocalsScript.sml` | `external_body_entry_state_rel`, `entry_register_arg_runtime`, `register_positional_args_local_ptrs` |
| Dispatch and entry-check runs (S1, no memory) | `lowering/moduleLoweringPropsScript.sml`, `lowering/entryDispatchPropsScript.sml`, `lowering/entryChecksPropsScript.sml` | `compile_selector_dispatch_linear_correct`, `compile_selector_checks_correct`, `compile_generate_runtime_shape`, `linear_dispatch_selects_function`, `compile_entry_checks_pass`, `entry_checks_pass` |
| Calldata decoder fragments and entry frames (proved, merged) | `lowering/actualDecoderPackagingScript.sml`, `lowering/actualRegistrationCodeScript.sml`, `lowering/actualEntryAllocationFrameScript.sml`, the `calldata*` theories, `lowering/entryArgPtrsScript.sml` | decoder fragments/adapters for arbitrary calldata, entry packaging, registration and allocation frames: use these for dynamic arguments instead of re-proving the decoder's execution |
| Argument decode (S1) | `lowering/entryDecodePropsScript.sml`, `lowering/entryDecodeStaticPropsScript.sml`, `lowering/entryDecodePlanPropsScript.sml`, `lowering/abiDecoder*Script.sml`, `lowering/abiDecodeStaticPropsScript.sml` | static and dynamic decoder correctness |
| `stmt_state_rel` and its parts | `lowering/stmtSimScript.sml`, `lowering/defs/compileEnvScript.sml`, `lowering/exprLoweringPropsScript.sml` | `state_rel`, `alloca_inv`, `alloca_room`, `local_ptrs_reserved` |
| Initial state | `lowering/vyperLoweringCorrectScript.sml` | `initial_venom_state_rel` (allocas empty, frontier 0) |

## Notes

- Weakly frozen: any helper lemma you introduce may be restated freely; only the theorem above is frozen.
- Two sibling runs prove the other admissions in other worktrees; their helpers get merged with yours later, so give your helper theories distinct, content-based names.
- 2026-11-05 move: this run's earlier work was ported onto a newer base. The theorem now lives in `loweringMemEntryReach`, and its statement changed in two places: `call_outcomes_ok am tx vs.vs_outcomes` (no `tops`), and a new conclusion conjunct `s0.vs_gas_readings = vs.vs_gas_readings` (the entry does no GAS reads, so the body starts with the caller's readings). The call-value revert helpers (bound labels, dispatch memory, value-check memory) are on this base in their repaired form. Existing proved helpers may need small repairs against the newer base.
- Don't edit existing theories outside `lowering/` leaf theories you created; if you need a change to an existing shared theory, put the new fact in a new leaf theory instead.

## Capacity gate and fleet outage (owner note, 2026-11-07 19:20 UTC)

- The remote-exec coordinator answers again; the previous run's blocker (curl 28 connection timeouts) is gone. Rerun `entryCapacitySourceProbeTheory` only if still needed.
- The natural-capacity candidate (an external parameter `DynArray[uint256, 2**251-1]`, memory size 2**256) is excluded by the frozen antecedent `lower_vyper_runtime_unit tops rpolicy = SOME unit`. `lower_vyper_runtime_unit` returns NONE unless `EVERY (fn_allocs_ok tops)` holds for every external, internal and fallback function (Python's 2**64 allocation limit, `Context.allocate_buffer`). `lower_vyper_runtime_unit_allocs_ok` (compileVyper) gives `fn_allocs_ok tops f` for each `MEM f exts` of `classify_functions tops`, and `fn_allocs_ok_body` (allocLimitsProps) turns that into `type_memory_bytes cenv ty < 2 ** 64` for every parameter in any compile env with the program's struct fields and events. The packaged descriptor's size is that `type_memory_bytes` (see `natural_capacity_package_location`), so every live parameter buffer is below 2**64 < dimword(:256). The evaluation test `allocation_limit_param_rejected` (evalCompilerAllocationLimit) checks the same rejection for a 2**256-byte parameter.
- So the frozen theorem is not refuted by this candidate: resolve C0 as excluded by that bound, drop the unverified source probe, and resume the main proof (the retained H1 work), using the bound as the exclusion invariant wherever capacity below dimword is needed.

## Upstream repair (owner note, 2026-11-07 20:30 UTC)

- The `calldataDynOwnedTheory` blocker is fixed by the owner: `calldata_owned_header_step[ownership_frame]` (lowering/calldataDynOwnedScript.sml:2593) timed out in `SIMP_RULE bool_ss [LET_THM] calldata_owned_interval_replace`; it now uses `SIMP_RULE (pure_ss ++ boolSimps.BOOL_ss) [LET_THM]` like `calldata_owned_counter_update`. `holbuild -j2 build calldataDynOwnedTheory` built it on the fleet: `remote vyper-hol:calldataDynOwnedTheory: done`, `holbuild finished in 1.387s`, exit 0.
- Resume the retained helper-closure audit and the main proof from there.

## Scope of repairs (owner note, 2026-11-07 20:30 UTC)

- Every theory added on this branch relative to the s3 tip (`git diff --name-only --diff-filter=A origin/bot/opus/seq-692-s3-mem-safety...HEAD -- lowering/`, e.g. `calldataFiniteEndpointsScript.sml`) is this task's helper: you may repair or restate it freely, including step-timeout repairs such as the `fs[EVERY_MEM]` at `calldataFiniteEndpointsScript.sml:94` (`calldata_valid_bytes_owned_endpoint[sequence]`). Rewrite with the specific EVERY fact instead of full-context `fs[EVERY_MEM]`.
- In the existing theories this branch already modifies (`actualRegistrationCode`, `calldataDynOwned`, `entryCompileIntervals`, `entryRejectCode`, `entrySourcePackages`, `helperBoundLabels`, `intCallCallee`), proof-text repairs for step timeouts are allowed; their theorem statements stay as they are.
- Still forbidden: changing tactic timeouts, new admissions, and edits to any other existing theory.

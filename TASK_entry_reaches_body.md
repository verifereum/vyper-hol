# TASK: S1: __entry reaches the selected external body start (external_entry_reaches_body)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (theorem in `lowering/externalEntryReachesBodyScript.sml`, theory `externalEntryReachesBody`)

## Theorem Statement (FROZEN)

```sml
Theorem external_entry_reaches_body:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
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
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
```

It is currently proved by `cheat` in `lowering/externalEntryReachesBodyScript.sml`.
Replace that cheat with a real proof.

**Do not modify this statement, or any definition it uses.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THE MAIN PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Helper lemmas go in new theory files under lowering/,
 * imported by externalEntryReachesBody, each built before
 * the main proof.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build externalEntryReachesBodyTheory` passes, and `external_entry_reaches_body` and every new helper have no CHEAT of their own.
2. Inherited admissions are expected and fine: many ancestor theories in this worktree are admitted with `cheat` as a local overlay (their sources differ from git's and are hidden from it), and some ancestors carry named admissions. The build log and kernel tags will show these. Don't try to prove, edit, or work around them, and never commit them; only the theorem above and your helpers must be cheat-free.
3. No duplicate or near-duplicate lemmas: search `lowering/*.sml`, `venom/**/*.sml` and `semantics/**/*.sml` before stating a new one, and reuse what exists.
4. No new axioms, no new premises on the frozen theorem, no change to any existing file other than `lowering/externalEntryReachesBodyScript.sml` (its `Ancestors` and the proof). In particular nothing under `semantics/`, `frontend/`, `lowering/defs/`, `lowering/proofs/`, `venom/`, `lowering/supported/`, and no `bodySim*`, `exprSimHyps`, `*Main`, `loweringRuntimeCorrect` edits.
5. New helper lemmas go in new theory files under `lowering/` with content-based names (e.g. `entryReachBody<Topic>Script.sml`), imported by `externalEntryReachesBody`. Helpers no other theory uses are `[local]`. Proofs stay under 50 lines each.
6. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout changes: every step must fit the default 2.5 s.
7. Commits: commit only `.sml` files under `lowering/` that you created or the target script (and this TASK file); never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*` or tool output. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample (program, call, state), state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
cd <worktree root, the directory with holproject.toml>
holbuild -j4 build externalEntryReachesBodyTheory
```

## Background

- What it says: when the call value check passes, the run from `__entry` (`run_context` on the initial Venom state `vs`) goes through the selector dispatch, the selected function's entry checks (`compile_entry_checks`) and its argument registration (`compile_register_positional_args`: an ALLOCA per parameter, then its ABI decode from calldata), and reaches the start `sa` of the selected function's guarded body in a state `s0` the body judgment can start from: `stmt_state_rel` in the body's compile env `cenv` with the source state `es0`, the GAS readings untouched, and every non-Error result from `s0` is a result of the run from `__entry`.
- The consumer is `lower_vyper_runtime_unit_body` / `lower_vyper_runtime_unit_correct` in `lowering/loweringRuntimeCorrectScript.sml`: read it to see exactly how each conjunct is used.
- `func` is existential: in the lowered unit the external bodies are blocks of `__entry` itself (`compile_generate_runtime`; `extract_context_with_internals` splits off only internal functions), reached by `JMP`.
- The dispatch and checks part: `lowering/externalEntryChecksScript.sml` proves `external_entry_reaches_checks`. That theory is being ported onto this base in parallel and will be merged into this worktree (a merge commit, with `lowering/externalEntryShapeScript.sml` for its shape lemmas) while you work; until it appears, work on the part after the checks and take this statement as given (it will not change):

```sml
Theorem external_entry_reaches_checks:
  !tops rpolicy unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) ==>
    ?rr lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st st' func
     s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, rr, tx.function_name, args, ([] : expr list), ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_entry_checks min_cds is_payable st = ((), st') /\
      fn_has_code st st' func /\
      vars_pc_only vs s0 /\ fresh_vars_wrt st s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = st.cs_current_bb /\
      s0.vs_inst_idx = LENGTH st.cs_current_insts /\
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
```

  Use it; don't re-prove the dispatch. `vars_pc_only vs s0` gives `s0.vs_gas_readings = vs.vs_gas_readings`.
- Arguments: `supported_program` allows dynamic parameter types (`String[n]`, `Bytes[n]`, `DynArray`, and aggregates of them), not only static ones (see `task090_external_dynamic_program` in `lowering/defs/bytecode/eval/evalCompilerSubsetAbiExternalScript.sml`). `valid_vyper_call` gives canonical calldata (`calldata_encodes`: selector ++ `enc (Tuple abi_types) (ListV abi_vals)`). The existing body-entry state relation `external_body_entry_state_rel` (`lowering/entryStateRelScript.sml`) covers word and static-ABI arguments only, and does not export `local_ptrs_reserved` or `stmt_state_rel`'s other parts (`alloca_inv`, `alloca_room`, `fmp_room`, `immutable_alloca_sep`, `immutable_base_zero`, the ALLOCA-size clause).
- A sibling effort (S3, memory safety of the same path, branch `bot/opus/seq-1000-s3-external-mem-reach`) built many helper theories for the dynamic calldata decoder's execution; it is NOT in this worktree. Several arbitrary-calldata decoder theories that are in this worktree are listed below.

## Domain Constraints

- Follow the lowering as defined; don't assume a supported subset narrower than `supported_program` gives.
- Don't edit shared ancestors (Completion Criteria 4). If you find you need a definition or statement change elsewhere, stop and report it with the exact change and why.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| The consumer | `lowering/loweringRuntimeCorrectScript.sml` | `lower_vyper_runtime_unit_body`, `lower_vyper_runtime_unit_correct` |
| Dispatch + checks reach | `lowering/externalEntryChecksScript.sml` | `external_entry_reaches_checks` and its shape lemmas |
| Entry checks run | `lowering/entryChecksPropsScript.sml` | `compile_entry_checks_pass`, `entry_checks_pass`, `valid_vyper_call_min_calldata_size` |
| Dispatch runs | `lowering/moduleLoweringPropsScript.sml`, `lowering/entryDispatchPropsScript.sml` | `vars_pc_only`, `vars_pc_only_trans`, `compile_selector_dispatch_linear_correct`, `compile_entry_checks_correct` |
| Body-start state relation (static args) | `lowering/entryStateRelScript.sml`, `lowering/entryArgPtrsScript.sml` | `external_body_entry_state_rel`, `body_entry_state_rel`, `register_positional_args_local_ptrs`, `entry_register_suffix_local_ptrs`, `bind_arguments_initial_local_ptrs` |
| Entry locals / env | `lowering/entryLocalsScript.sml`, `lowering/bodySimEntryScript.sml` | `compile_register_positional_args_reserved`, `external_entry_locals`, `external_entry_declared`, `compile_register_positional_args_body_inv` |
| Code containment | `lowering/actualDecoderPackagingScript.sml`, `lowering/actualRegistrationCodeScript.sml`, `lowering/proofs/loweringShapePropsScript.sml` | `external_entry_fn_has_code`, `register_positional_args_suffix_extends`, `external_function_registration_boundary`, `compile_register_positional_args_shape`, `compile_entry_checks_shape` |
| Allocation frames on the entry path | `lowering/actualEntryAllocationFrameScript.sml`, `lowering/actualAllocExecScript.sml`, `lowering/actualAllocCreditScript.sml`, `lowering/actualDecoderSitesScript.sml` | `vars_pc_only_allocas`, `compile_selector_dispatch_linear_allocas`, allocation execution/credits |
| Arbitrary-calldata registration and decoder (dynamic args) | `lowering/calldataRegistrationScript.sml`, `lowering/calldataRegistrationExecScript.sml`, `lowering/calldataRegistrationLocalsScript.sml`, `lowering/calldataReconstructionScript.sml`, `lowering/calldataRecursive*Script.sml`, `lowering/calldataDyn*Script.sml`, `lowering/calldataBytes*Script.sml`, `lowering/calldataWord*Script.sml`, `lowering/calldataBulk*Script.sml`, `lowering/calldataFinite*Script.sml`, `lowering/calldataAggregateTypedScript.sml`, `lowering/calldataMembersScript.sml`, `lowering/calldataSafeIterationScript.sml`, `lowering/calldataChildFrameScript.sml` | registration boundaries, decoder execution over calldata, decoded values typed in memory, source scopes for decoded arguments |
| Argument decode (S1) | `lowering/entryDecodePropsScript.sml`, `lowering/entryDecodeStaticPropsScript.sml`, `lowering/entryDecodePlanPropsScript.sml`, `lowering/entryDecodeStructureScript.sml`, `lowering/abiDecodeStaticPropsScript.sml`, `lowering/abiDecoder*Script.sml`, `lowering/abiCanonicalHeadSizeScript.sml`, `lowering/abiDecodeRangesScript.sml` | static and dynamic decoder correctness |
| `stmt_state_rel` and its parts | `lowering/exprLoweringPropsScript.sml`, `lowering/defs/compileEnvScript.sml`, `venom/defs/venomMemDefsScript.sml`, `lowering/stmtSimScript.sml` | `stmt_state_rel`, `state_rel`, `alloca_inv`, `alloca_room`, `fmp_room`, `immutable_alloca_sep`, `immutable_base_zero`, `local_ptrs_reserved`; search for existing theorems concluding `alloca_room`/`fmp_room` at a function entry (internal calls do this) |
| Fragment framework | `lowering/fragExecScript.sml`, `lowering/emitHelperPropsScript.sml` | `frag_exec`, `fn_has_code`, `fresh_vars_wrt`, `not_fresh_at` |
| The lowering | `lowering/defs/moduleLoweringScript.sml`, `lowering/defs/compileVyperScript.sml`, `lowering/defs/vyperCompilerScript.sml`, `lowering/compileVyperScript.sml`, `lowering/defs/abiEncoderScript.sml` | `lower_vyper_runtime_unit`, `run_lowering`, `compile_generate_runtime`, `package_external_fn`, `compile_entry_checks`, `compile_register_positional_args`, `compile_decode_args`, `compile_abi_decode_to_buf`, `compile_guarded_body` |
| Initial state | `lowering/vyperLoweringCorrectScript.sml` | `initial_venom_state_rel` (vars empty, allocas empty, frontier 0) |
| Supported subset | `lowering/supported/` | `supported_program` |

## Notes

- Weakly frozen: any helper lemma you introduce may be restated freely; only the theorem above is frozen.
- Other workers prove sibling admissions of S1 in other worktrees and their helpers get merged with yours later, so give your helper theories distinct, content-based names.

## Upstream repair (owner note)

The external prerequisite from the last run is repaired. `calldata_owned_header_step[ownership_frame]` in `lowering/calldataDynOwnedScript.sml:2587` hit the 2.5s tactic timeout. The fix is proof-only: three inline `SIMP_RULE` terms are hoisted to `[local]` theorems, and no statement changes. It is commit `327d048f3` on the s1-entry-return base (c1efb40ad's hunk for that file), and it is applied in this worktree.

`holbuild -j2 build calldataDynOwnedTheory` at the default limit: `calldataDynOwnedTheory built` (exit 0).

That file is a protected ancestor: don't edit or commit it. Continue from `C1.3.1.registration.inputs.source_constructor_config`: build `entryReachBodySourceArrayConstructorTheory`, then carry on toward the frozen theorem.

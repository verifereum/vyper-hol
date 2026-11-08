# TASK: S1: compose external_entry_reaches_body from the proved entry machinery

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
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
Proof
  cheat
QED
```

## Completion Criteria

1. `holbuild -j4 build externalEntryReachesBodyTheory` passes at the default 2.5 s step limit, and the target theorem and every new helper have no CHEAT of their own.
2. Inherited admissions are fine: the s1-entry-return piece leaves of this branch (and the sibling leaf named under Notes) carry named `cheat`s. Don't prove, edit or work around them.
3. No duplicate lemmas: search `lowering/*.sml` (the `entryReachBody*` theories above all), `venom/**/*.sml` and `semantics/**/*.sml` before stating a new one, and reuse what exists.
4. No new axioms, no new premises on the frozen theorem, no edits to existing files other than the target script (its `Ancestors` and the proof). Nothing under `semantics/`, `frontend/`, `lowering/defs/`, `lowering/proofs/`, `venom/`, `lowering/supported/`, and no `bodySim*`, `exprSimHyps`, `*Main`, `loweringRuntimeCorrect`, or existing `entryReachBody*`/`externalEntry*` theory edits.
5. New helpers go in new theory files under `lowering/` with content-based names, imported by the target theory. Helpers no other theory uses are `[local]`. Proofs stay under 50 lines each.
6. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout changes.
7. Commit only `.sml` files under `lowering/` you created, the target script and this TASK file; never `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*` or tool output. End every commit message with:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** give a concrete counterexample (program, call, state), the tightest sufficient fix to the statement, and stop. Don't weaken the statement.

## Build

```
cd <worktree root, the directory with holproject.toml>
holbuild -j4 build externalEntryReachesBodyTheory
```

## Background

- All the semantic work is proved in the `entryReachBody*` theories; this task composes them. One part is admitted: `entry_body_state_assembly` (`lowering/entryReachBodyStateAssemblyScript.sml`), which gives `stmt_state_rel` at the end of registration. Another alan run proves it in a sibling worktree. Use it as stated; its `cheat` is the one inherited admission you may rely on, besides the s1-entry-return piece leaves.
- The chain, all for the same `func` (the `__entry` function):
  1. `entry_reaches_checks_root` (`entryReachBodyRootChecksScript.sml`) reaches the start of the selected function's entry checks in `s0` with `vars_pc_only vs s0`, the root lookup of `func`, and the back-simulation to `run_context … vs`. Its raw-return argument `rr` is existential: identify the package with the frozen statement's `lookup_raw_return_or_F` one via `entry_selected_source_code` (`entryReachBodySelectedCodeScript.sml`) and determinism of `set_external_package_target`/`package_external_fn`. Take `func` from the root lookup; `fn_has_code` alone doesn't identify functions.
  2. `entry_registration_initial_endpoint` (`entryReachBodyRegistrationInitializationScript.sml`) runs the checks. The value check passes by `send_call_value … = (INL (), es0)`; the calldata size bounds come from `valid_vyper_call` (`valid_vyper_call_min_calldata_size`, `entryChecksPropsScript.sml`). It ends with `entry_prefix_witness … 0` at the registration start and the allocation resources.
  3. `entry_registration_full_run` (`entryReachBodyRegistrationIterationScript.sml`) runs every positional argument's registration to `t`. Its `fn = mk_raw_function "__entry" (all_blocks entry_end)` comes from `entry_selected_source_code` (`func.fn_blocks = all_blocks se`); `site` and the frontier from `entry_root_zero_frontier`/`entry_checks_root_frontier` (`entryReachBodyInitialResourcesScript.sml`).
  4. `entry_body_state_assembly` gives `stmt_state_rel` at `t`.
  5. The rest of the conclusion: `s0 := t`, `sa := registered`; `t.vs_gas_readings = vs.vs_gas_readings` from `entry_loop_fields vs t`; `local_ptrs_reserved cenv sa` from `compile_register_positional_args_reserved` (`entryLocalsScript.sml`); `~block_is_terminated sa`, `fn_has_code sa st' func` and `fn_inst_ids_distinct func` from the selected-code facts; the back-simulation by chaining each step's `run_from` implication into step 1's.
- Read `lower_vyper_runtime_unit_body` in `lowering/loweringRuntimeCorrectScript.sml` for how each conjunct is consumed.

## Notes

- Keep the proof of the frozen theorem short: put each glue step (package identification, the check-pass premises, the final structural conjuncts) in a `[local]` lemma or a new `entryReachBody<Topic>Script.sml` helper theory.

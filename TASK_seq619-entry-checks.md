# TASK: the run from __entry reaches the selected external function's entry checks

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/ (theorem in lowering/loweringRuntimeCorrectScript.sml)

## Theorem Statement (FROZEN)

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

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build loweringRuntimeCorrectTheory` passes; the proof of `external_entry_reaches_checks` has no cheat. The other cheats already in that file (`external_body_source_ok`, `external_entry_reaches_body`, `external_body_frame`, `external_frame_ret_ok`, `external_body_revert_data_reverts`, and the probe in `compile_stmt_ret_ty` if still there) are out of scope: leave them and their statements alone.
2. No new cheats, axioms or definitions changed. Helper lemmas may go in this file (as `[local]` when only used here) or in the theory where they belong (e.g. lowering/moduleLoweringPropsScript.sml, lowering/entryDispatchPropsScript.sml, lowering/fragExecScript.sml).
3. Every proof step under holbuild's default 2.5s tactic timeout; never raise or disable it. No `TRY`/`ORELSE` around `metis_tac` or other search: select goals with `>-`, `>~`, `>|`.
4. No duplicate lemmas: search for existing ones first.

## Build

```
holbuild -j4 build loweringRuntimeCorrectTheory
```
(from the project root, the directory with holproject.toml; use `--max-heap`, never `--maxheap`)

## Background

S1 (`lower_vyper_runtime_unit_correct` at the bottom of loweringRuntimeCorrectScript.sml) relates the lowered Venom unit's run to the Vyper source call. `external_entry_value_revert` (proved in this file from this helper plus `entry_checks_nonpayable_value`) handles a nonpayable function called with value. This helper is the dispatch glue: `run_context` starts `__entry`, whose code is `compile_generate_runtime`'s blocks from `initial_compile_state "__entry"` (Linear dispatch, forced by `lowering_policy_ok`); the linear selector dispatch jumps to `"fn_" ++ tx.function_name`, the block `compile_external_fn_bodies` opens for the selected function, which starts with `compile_entry_checks`.

## Domain Constraints

- vyper-hol rules: read AGENTS.md at the project root. No interactive `g`/`e` sessions; edit and build with holbuild.
- Don't change executable definitions (anything under lowering/defs/ or semantics/).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| target | lowering/loweringRuntimeCorrectScript.sml | the theorem, and its consumer external_entry_value_revert |
| unit construction | lowering/defs/compileVyperScript.sml (lower_vyper_runtime_unit_def ~1352, package_external_fn_def ~959, set_external_package_target_def ~1218, classify_functions, build_selectors, compute_selector) | how the runtime unit and packages are built |
| run_lowering | lowering/defs/vyperCompilerScript.sml (run_lowering_def, lowering_policy_ok_def, extract_context_with_internals) | context extraction, Linear dispatch |
| runtime code | lowering/defs/moduleLoweringScript.sml (compile_generate_runtime_def ~785, compile_external_fn_bodies_def ~756, compile_selector_dispatch_linear) | code layout |
| dispatch | lowering/moduleLoweringPropsScript.sml (compile_selector_dispatch_linear_correct ~431, runs_through_def, vars_pc_only_def, linear_dispatch_target) | dispatch reaches linear_dispatch_target |
| selector choice | lowering/entryDispatchPropsScript.sml (linear_dispatch_selects_function, linear_selectors_lt, lookup_function_external_mem) | the dispatch target is "fn_" ++ name |
| entry checks | lowering/entryChecksPropsScript.sml (entry_checks_pass, entry_checks_nonpayable_value) | consumers of the state this helper produces |
| frag/run lemmas | lowering/fragExecScript.sml (fn_has_code, frag_exec_def, run_context_run_blocks, run_blocks_run_from_no_phi, fn_has_code_split/mid) | running compiled code |
| shape | lowering/proofs/loweringShapePropsScript.sml (compile_generate_runtime_shape ~11871, compile_external_fn_bodies_shape, run_lowering_source_unit_ok ~12560) | block structure of the runtime unit, entry-block labels |
| compile monad | lowering/defs/compileEnvScript.sml (comp_bind, new_block, fresh_label ~616, compile_state_ok ~841), lowering/emitHelperPropsScript.sml | label freshness |
| supported program | lowering/supported/supportedProgramScript.sml, supportedNamesScript.sml (supported_selectors_distinct, ALL_DISTINCT supported_function_names), supportedDeclsScript.sml (no public getters) | premises |
| source/e2e | lowering/e2eDefsScript.sml (valid_vyper_call_def, source_typing_ok_def), lowering/vyperLoweringCorrectScript.sml (initial_venom_state_rel_def, venom_env_rel_def, initial_venom_state_calldata_length) | premises on the call and the initial Venom state |

## Notes

The theorem's fn_has_code covers only the entry-check segment (compile_entry_checks opens no block), so only the label "fn_" ++ name needs to be unique among the entry function's blocks: fresh labels start with "@", internal function labels with "internal ", and supported_program makes external function names distinct.

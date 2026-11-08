# TASK: S1 body entry: stmt_state_rel at the end of argument registration (entry_body_state_assembly)

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: project root (theorem in `lowering/entryReachBodyStateAssemblyScript.sml`, theory `entryReachBodyStateAssembly`)

## Theorem Statement (FROZEN)

```sml
Theorem entry_body_state_assembly:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\
  source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
       <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
    (INL (), es0) /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
       (mut, F, lookup_raw_return_or_F (NONE : num option)
                   tx.function_name External tops,
        tx.function_name, args, ([] : expr list), ret, fbody)) =
    (lbl, ce, pos, cds, pay, F, key, ut, view, fbody, rt) /\
  compile_register_positional_args ce pos 4 start = (cef, registered) /\
  compile_guarded_body cef F key ut view fbody rt registered = ((), final) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  MEM fn unit.cu_context.ctx_functions /\ fn_inst_ids_distinct fn /\
  fn_has_code start final fn /\
  entry_prefix_witness fn (type_env tops) args tx.args (LENGTH args)
    cef registered t /\
  alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
  abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt final t /\
  (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < registered.cs_next_id) /\
  entry_loop_fields vs t /\ cef.ce_is_ctor = F ==>
  stmt_state_rel unit.cu_context fn cef
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 t
Proof
  cheat
QED
```

## Completion Criteria

1. `holbuild -j4 build entryReachBodyStateAssemblyTheory` passes at the default 2.5 s step limit, and the target theorem and every new helper have no CHEAT of their own.
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
holbuild -j4 build entryReachBodyStateAssemblyTheory
```

## Background

- This is one of two leaves the frozen S1 piece `external_entry_reaches_body` (`lowering/externalEntryReachesBodyScript.sml`) is split into. Its premises are the frozen piece's premises plus exactly what `entry_registration_full_run` (`lowering/entryReachBodyRegistrationIterationScript.sml`, proved) concludes about the state `t` where the registration of every positional argument ends. Its conclusion is the piece's `stmt_state_rel` conjunct at that state. The other leaf composes the piece from this one; don't do that part here.
- Unfold `stmt_state_rel` (`lowering/exprLoweringPropsScript.sml:485`) into its seven parts and get each from an existing boundary:
  - `state_rel`: `entry_runtime_state_rel` (`lowering/entryReachBodyRuntimeStateScript.sml`). Its field equalities come from `entry_loop_fields vs t` and `initial_venom_state_rel`. `local_ptrs_rel fn cef [env] t` comes from `entry_prefix_witness fn … (LENGTH args) cef registered t` (each argument's `PtrVar (Var vname)` names an ALLOCA of `fn` holding its value) and `bind_arguments`. `storage_vars_rel`, `transient_vars_rel`, `ce_module = NONE` and `immutable_section_layout` hold for the packaged `ce`, and registration changes only `ce_vars` (`compile_register_positional_args_cenv`).
  - `alloca_inv t`: a premise.
  - `alloca_room`: `entry_frontier_alloca_room` (`entryReachBodyAllocationRoomScript.sml`) from `alloca_frontier_inv`, with the checked budget bound from `lower_vyper_runtime_unit`.
  - `fmp_room`: `entry_runtime_fmp_room` (`entryReachBodyFmpScript.sml`).
  - `immutable_alloca_sep`, `immutable_base_zero`: both should be vacuous or trivial under `cef.ce_is_ctor = F`; check against their definitions in `exprLoweringPropsScript.sml`.
  - the ALLOCA-size clause: from `abi_alloca_history (fn_insts fn) t`.
- Read `lower_vyper_runtime_unit_body` in `lowering/loweringRuntimeCorrectScript.sml` to see how the piece's conjunct is consumed.

## Notes

- The proved registration machinery is in the `entryReachBodyRegistration*` theories; `entry_slot_witness`/`entry_prefix_witness` are defined in `entryReachBodyRegistrationSlotWitnessScript.sml`.
- Another alan run proves the frozen piece from this leaf in a sibling worktree; its helper theories are merged with yours later, so give yours distinct, content-based names.

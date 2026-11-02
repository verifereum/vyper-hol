# TASK: O1 schedule decomposition with instruction-id distinctness in o1_ctx_shape

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/compiler/

## Theorem Statement (FROZEN)

`o1_ctx_shape` (venom/compiler/o1PassContractScript.sml) now includes
`ctx_inst_ids_distinct ctx`. The schedule decomposition must establish it
for every stage context and every observed unit. These statements, in
`venom/compiler/o1ComposeSupportScript.sml`, are frozen:

```sml
Theorem o1_schedule_stages:
  EVERY (o1_step_contract rp) passes /\
  run_named_fn_schedules execute_configured_fn_pass rp passes names u s =
    SOME (u',s') /\
  o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s ==>
  unit_labels_wf u' /\ ir_supply_inst_ok s' /\
  ?stage.
    stage 0 = u.cu_context /\ stage (LENGTH passes) = u'.cu_context /\
    (!k. k <= LENGTH passes ==>
      o1_ctx_shape (stage k) /\
      (stage k).ctx_entry = u.cu_context.ctx_entry /\
      (stage k).ctx_global_reserved = u.cu_context.ctx_global_reserved /\
      ctx_fn_names (stage k) = ctx_fn_names u.cu_context) /\
    (!k. k < LENGTH passes ==>
      ctx_pass_stage rp (EL k passes) any_view (stage k) (stage (SUC k)) /\
      (callee_first names u.cu_context.ctx_functions ==>
       ctx_pass_stage rp (EL k passes) (walk_view rp (DROP (SUC k) passes))
         (stage k) (stage (SUC k))))
Theorem mapped_pass_stage:
  o1_step_contract rp pass /\
  run_mapped_functions rp pass u s = SOME (u',s') /\
  o1_ctx_shape u.cu_context /\ ALL_DISTINCT (unit_label_namespace u) /\
  ir_supply_inst_ok s ==>
  unit_labels_wf u' /\ ir_supply_inst_ok s' /\ o1_ctx_shape u'.cu_context /\
  u'.cu_context.ctx_entry = u.cu_context.ctx_entry /\
  u'.cu_context.ctx_global_reserved = u.cu_context.ctx_global_reserved /\
  ctx_fn_names u'.cu_context = ctx_fn_names u.cu_context /\
  ctx_pass_stage rp pass any_view u.cu_context u'.cu_context
```

Also frozen, byte for byte: every theorem statement and definition in
`o1PassContractScript.sml`, `o1ScheduleDecompScript.sml`,
`o1ComposeSupportScript.sml`, `o1PipelineComposeScript.sml` and
`o1PipelineCorrectScript.sml`, and `venomFnScheduleRunnerScript.sml`.

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

Weakly frozen: theorems and the proof-internal definitions
(`chain_facts`, `partial_schedule`, `mixed_fns`, `stage_ctx`) in
`o1FnScheduleDecompHelpersScript.sml`, `o1FnScheduleDecompScript.sml`,
`o1ScheduleDecompHelpersScript.sml` and `o1PartialScheduleScript.sml` may
gain premises, conclusions or conjuncts when the proof needs them, as long
as their callers in those files and the frozen theories still discharge
them. `o1_ctx_shape_MAP_replace` is false as stated now (the replacement
function's ids may clash); give it the disjointness premise it needs.
Say in the report which of these you changed and how.

## Completion Criteria

1. `holbuild -j4 build o1PipelineCorrectTheory concretizeStagePtrTheory concretizeStageSimTheory`
   passes with zero failures.
2. No new cheat. The cheats already present (`git grep -n cheat` at the
   task's start commit, in o1PipelineCorrectScript.sml and the two
   concretizeStage scripts) stay as they are; no others.
3. No duplicate or near-duplicate lemmas.

**If a frozen theorem is false as stated:**
- Produce a HOL4 counterexample (`EVAL` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build o1PipelineCorrectTheory concretizeStagePtrTheory concretizeStageSimTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

ConcretizeMemLoc keys imported callee allocations by ALLOCA instruction
id, so its stage contract needs ids distinct across the context, as
Python's global counter makes them. That fact now sits in `o1_ctx_shape`,
which every step and stage contract assumes of its input. The runner
(`run_configured_fn_passes`) checks `unit_global_inst_ids_distinct` of the
unit after each function's passes, but the stage contexts mix functions at
different points of their pass chains, so their distinctness has to come
from the supply. The argument is in the SML comment above
`partial_schedule_def` in `o1PartialScheduleScript.sml`.

## Domain Constraints

- holbuild only (no Holmake, no hol4-mcp). Default tactic timeout; never
  raise it. No `TRY`/`ORELSE` around metis or any search tactic.
- No `let` in theorem statements. No new axioms. No cheats left anywhere
  beyond the pre-existing ones.
- Executable definitions (the runner, the passes, the semantics, the IR
  supply) are frozen.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Shape and step contract | venom/compiler/o1PassContractScript.sml | o1_ctx_shape, o1_fn_shape, fn_pass_step, fresh_names_ok, o1_step_contract |
| Runner | venom/defs/venomFnScheduleRunnerScript.sml | run_configured_fn_passes, ir_supply_covers_*, ir_supply_extends |
| Supply ids | venom/defs/irSupplyScript.sml | fn_ir_inst_ids, unit_ir_inst_ids |
| Wf defs | venom/defs/venomWfScript.sml | ctx_inst_ids_distinct, fn_inst_ids_distinct, wf_function |
| Unit wf | venom/defs/venomCompilerWfScript.sml | unit_global_inst_ids_distinct, unit_wf |
| Fn chain | venom/compiler/o1FnScheduleDecompScript.sml, o1FnScheduleDecompHelpersScript.sml | fn_chain, run_configured_fn_passes_decomp |
| Partial schedule | venom/compiler/o1PartialScheduleScript.sml | chain_facts, partial_schedule, partial_schedule_step |
| Schedule decomp | venom/compiler/o1ScheduleDecompScript.sml, o1ScheduleDecompHelpersScript.sml | stage_ctx shape |
| Compose | venom/compiler/o1ComposeSupportScript.sml, o1PipelineComposeScript.sml | consumers |

## Notes
- `fn_ir_inst_ids` (supply) and the id list in `ctx_inst_ids_distinct` /
  `fn_inst_ids_distinct` are spelled differently; prove them equal once.
- Prune (`prune_unit_fcg_unreachable`) keeps a sublist of the functions,
  and the source unit is `unit_wf`, which gives distinctness
  (`unit_wf_unit_global_inst_ids_distinct`).
- `concretizeAnalysisAntecedentProbeScript.sml` is a diagnostic probe; if
  it breaks, delete it rather than fix it.
- Another alan run proves the two concretizeStage theorems in a different
  worktree; here they stay cheated. Don't touch those two files.

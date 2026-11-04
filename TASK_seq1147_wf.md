# TASK: tail merge preserves wf_function

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

In `venom/passes/tail_merge/proofs/tailMergeWfScript.sml`:

```sml
Theorem tail_merge_fn_wf_function:
  !func. wf_function func ==> wf_function (tail_merge_fn func)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

Definitions it uses (do not modify any of them):
- `tail_merge_fn`, `block_sigs`, `compute_merge_map`, `block_signature`:
  `venom/passes/tail_merge/defs/tailMergeDefsScript.sml`
- `subst_block_labels_fn/_block/_inst`, `subst_label_map_inst`:
  `venom/defs/cfgTransformScript.sml` (~150-200)
- `wf_function` and its parts (`fn_has_entry`, `bb_well_formed`,
  `fn_succs_closed`, `fn_inst_ids_distinct`): `venom/defs/venomWfScript.sml`
  (~458-530)

## Completion Criteria

1. `holbuild -j4 build tailMergeWfTheory` passes at the default tactic
   timeout with proof steps on.
2. No `cheat` left in `venom/passes/tail_merge/proofs/tailMergeWfScript.sml`
   or `tailMergeMapScript.sml`; no new cheat anywhere.
3. No new axioms or definitions, no `TRY`/`ORELSE` around `metis_tac` or
   other search, no timeout overrides.
4. Edit only `tailMergeWfScript.sml` and `tailMergeMapScript.sml` (both in
   `venom/passes/tail_merge/proofs/`); new lemmas go there. Don't edit
   other theories: another proof job is changing them in parallel.

**If the theorem is false as stated:** produce a concrete counterexample,
state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild -j4 build tailMergeWfTheory
```

## Background

Tail merge (Venom IR compiler pass) finds halting, self-contained,
ALLOCA-free non-entry blocks with equal alpha-renamed signatures, maps each
duplicate label to a keeper (`compute_merge_map`), rewrites label operands
of terminators and PHIs through that map, and drops the duplicate blocks.
The sibling theorem `tail_merge_fn_ssa_form` in the same file is already
proved and shows the style.

## Domain Constraints

- Stay with the existing definitions; don't add new ones.
- Use holbuild only (no Holmake).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Merge-map lemmas | `venom/passes/tail_merge/proofs/tailMergeMapScript.sml` | `compute_merge_map_SND_not_FST`, `_FST_subset`, `_SND_subset`, `_not_entry`, `_halting`, `block_sigs_*`, `lookup_block_*` |
| subst_block_labels simp lemmas | `venom/passes/tail_merge/proofs/tailMergeHelpersScript.sml` | label/opcode/outputs/id unchanged by substitution |
| Pass definition | `venom/passes/tail_merge/defs/tailMergeDefsScript.sml` | |
| CFG transforms | `venom/defs/cfgTransformScript.sml` | substitution, `bb_is_halting`, `bb_self_contained` |
| wf definitions | `venom/defs/venomWfScript.sml` | `wf_function`, `bb_well_formed`, `fn_succs_closed`, `fn_inst_ids_distinct` |
| Instruction defs | `venom/defs/venomInstScript.sml` | `is_terminator`, `is_block_label_opcode`, `bb_succs`, `get_successors`, `fn_insts_blocks` |
| Similar proof | `venom/passes/simplify_cfg/proofs/simplifyCfgWffnScript.sml` | wf_function preservation for a pass that also substitutes labels and removes blocks |
| Similar proof | `venom/passes/remove_unused/proofs/removeUnusedStructProofsScript.sml` | `rusp_preserves_wf_function`, sublist lemmas |

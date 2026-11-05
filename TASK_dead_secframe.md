# TASK: Deploy piece Dead: the immutables section's dead bytes are fixed by its live bytes (imm_section_dead_frame)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (theorem in `lowering/proofs/ctorDeployDeadSectionFrameScript.sml`, theory `ctorDeployDeadSectionFrame`)

## Theorem Statement (FROZEN)

```sml
Theorem imm_section_dead_frame:
  !tops sec1 sec2.
    struct_args_unique tops /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
         EL j sec2 = EL j sec1) ==>
    imm_section_dead tops sec2 = imm_section_dead tops sec1
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build ctorDeployDeadSectionFrameTheory` passes with zero failures, and `imm_section_dead_frame` and every new helper have no CHEAT.
2. No duplicate or near-duplicate lemmas: search `lowering/**/*.sml` and `semantics/**/*.sml` before stating a new one, and reuse what exists. Existing `[local]` lemmas in other theories can't be reused or copied; prove what you need under a new name only if no exported lemma covers it.
3. No new axioms, no new premises on the frozen theorem, no changes to any definition, and no edits to existing files except `lowering/proofs/ctorDeployDeadSectionFrameScript.sml`: nothing under `lowering/defs/`, `semantics/`, `venom/`, `frontend/`, and no edit to any other existing theory. Some ancestors are admitted locally with `cheat` in this worktree (uncommitted overlay edits); they are other runs' work. Don't touch or rely on their being cheats, and never stage them. Sibling helper theorems in `lowering/proofs/ctorDeployDead*Script.sml` other than yours may still be cheated (parallel runs); you may use their statements, but don't edit those files.
4. New helper lemmas go in `lowering/proofs/ctorDeployDeadSectionFrameScript.sml` or in new theory files `lowering/proofs/ctorDeployDeadSectionFrame*Script.sml`, added to `ctorDeployDeadSectionFrame`'s `Ancestors`. Proofs stay under 50 lines each; give each case of an induction longer than 3 tactics its own lemma.
5. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. Every proof step must fit the default 2.5 s tactic timeout; no timeout changes.
6. Commits: stage files by name, only `.sml` files you created or edited under `lowering/proofs/` (and this TASK file); never `git add -u` or `-A`, since the overlay's edits to other files must not be committed. Never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*`, `alan-ref/`. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build ctorDeployDeadSectionFrameTheory
```

## Background

- `imm_section_dead tops sec j` (`lowering/proofs/ctorDeployDefsScript.sml`): byte `j` of the immutables section `sec` is dead in some immutable's value. Immutable `name : ty` sits at `compute_immutables_len sft pre` (the sum of `type_mem_bytes sft` of the earlier immutables; `lowering/defs/compileVyperScript.sml`) and its dead bytes are `mem_dead_bytes` at type `evaluate_type (type_env tops) ty`.
- The theorem is `dead_wf`'s returndata clause for the deployment's dead bytes (`deploy_dead`, used by `deploy_dead_wf` in `lowering/proofs/ctorDeployDeadScript.sml`, already proved from this theorem).
- `struct_args_unique tops` gives `type_memory_size tv = type_mem_bytes sft ty` (`make_struct_fields_map_memory_size` with `type_mem_bytes_type_memory_bytes`), so the immutables' regions are disjoint.
- `mem_dead_bytes_frame` and `mem_dead_bytes_range` (`lowering/proofs/ctorDeployDeadSectionScript.sml`) are the per-value facts; the frame lemma is being proved in a parallel run and may still be cheated here.

## Domain Constraints

- Follow the definitions as they are; don't assume a narrower program subset than the premises give.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Dead-byte definitions | `lowering/proofs/ctorDeployDefsScript.sml` | `imm_section_dead`, `mem_dead_bytes` |
| Per-value facts | `lowering/proofs/ctorDeployDeadSectionScript.sml` | `mem_dead_bytes_range`, `mem_dead_bytes_frame` |
| Layout | `lowering/defs/compileVyperScript.sml` | `compute_immutables_len`, `type_mem_bytes`, `make_struct_fields_map` |
| Size agreement | `lowering/structFieldsPropsScript.sml, lowering/entryStateRelScript.sml` | `make_struct_fields_map_memory_size`, `type_mem_bytes_type_memory_bytes` |
| Immutable section facts | `lowering/proofs/immutableSectionRelScript.sml, lowering/proofs/immutableRelationScript.sml, lowering/defs/immutableSectionScript.sml` | existing lemmas on decl decomposition and offsets |

## Notes

- Weakly frozen: helper lemmas you add may be restated freely; only the theorem above is frozen.

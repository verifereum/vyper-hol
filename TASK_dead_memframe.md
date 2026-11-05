# TASK: Deploy piece Dead: mem_dead_bytes reads only its value's live bytes (mem_dead_bytes_frame)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (theorem in `lowering/proofs/ctorDeployDeadSectionScript.sml`, theory `ctorDeployDeadSection`)

## Theorem Statement (FROZEN)

```sml
Theorem mem_dead_bytes_frame:
  !sec1 sec2 off tv.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
         ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build ctorDeployDeadSectionTheory` passes with zero failures, and `mem_dead_bytes_frame` and every new helper have no CHEAT.
2. No duplicate or near-duplicate lemmas: search `lowering/**/*.sml` and `semantics/**/*.sml` before stating a new one, and reuse what exists. Existing `[local]` lemmas in other theories can't be reused or copied; prove what you need under a new name only if no exported lemma covers it.
3. No new axioms, no new premises on the frozen theorem, no changes to any definition, and no edits to existing files except `lowering/proofs/ctorDeployDeadSectionScript.sml`: nothing under `lowering/defs/`, `semantics/`, `venom/`, `frontend/`, and no edit to any other existing theory. Some ancestors are admitted locally with `cheat` in this worktree (uncommitted overlay edits); they are other runs' work. Don't touch or rely on their being cheats, and never stage them. Sibling helper theorems in `lowering/proofs/ctorDeployDead*Script.sml` other than yours may still be cheated (parallel runs); you may use their statements, but don't edit those files.
4. New helper lemmas go in `lowering/proofs/ctorDeployDeadSectionScript.sml` or in new theory files `lowering/proofs/ctorDeployDeadSectionMem*Script.sml`, added to `ctorDeployDeadSection`'s `Ancestors`. Proofs stay under 50 lines each; give each case of an induction longer than 3 tactics its own lemma.
5. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. Every proof step must fit the default 2.5 s tactic timeout; no timeout changes.
6. Commits: stage files by name, only `.sml` files you created or edited under `lowering/proofs/` (and this TASK file); never `git add -u` or `-A`, since the overlay's edits to other files must not be committed. Never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*`, `alan-ref/`. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build ctorDeployDeadSectionTheory
```

## Background

- `mem_dead_bytes sec off tv i` (`lowering/proofs/ctorDeployDefsScript.sml`) says byte `i` of a memory-layout buffer `sec` is dead in the value of type `tv` stored at `off`: past a dynamic bytestring's length, or in a dynamic array's slots past its length, recursively through tuples, structs and arrays. It reads `sec` only through `mem_word_at` at length words.
- The theorem: two buffers of equal length that agree on every byte of the value's region `[off, off + type_memory_size tv)` that isn't dead in the first have the same dead bytes.
- `mem_dead_bytes_range` (same file, proved) bounds dead bytes to the region; `mem_word_at` (`lowering/defs/valueEncodingScript.sml`) zero-pads past the buffer's end.
- Consumers: `imm_section_dead_frame` (`lowering/proofs/ctorDeployDeadSectionFrameScript.sml`) and through it `deploy_dead_wf` (`lowering/proofs/ctorDeployDeadScript.sml`).

## Domain Constraints

- Follow the definitions as they are; don't assume a narrower program subset than the premises give.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Dead-byte definitions | `lowering/proofs/ctorDeployDefsScript.sml` | `mem_dead_bytes` (and its `_list`/`_fields` mutual parts, induction `mem_dead_bytes_ind`) |
| Range lemma | `lowering/proofs/ctorDeployDeadSectionScript.sml` | `mem_dead_bytes_range` |
| Memory encoding | `lowering/defs/valueEncodingScript.sml` | `mem_word_at`, `mem_bytes_at`, `type_memory_size` |
| Storage twin | `lowering/defs/compileEnvScript.sml, lowering/accountsRelPropsScript.sml` | `dead_bytes` and its frame `dead_bytes_live_frame` / `storage_agree_storage_dead`: the same fact for storage layout |

## Notes

- Weakly frozen: helper lemmas you add may be restated freely; only the theorem above is frozen.

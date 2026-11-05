# TASK: Deploy piece Dead: immutables_section_rel ignores the section's dead bytes (immutables_section_rel_dead)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (theorem in `lowering/proofs/ctorDeployDeadSectionRelScript.sml`, theory `ctorDeployDeadSectionRel`)

## Theorem Statement (FROZEN)

```sml
Theorem immutables_section_rel_dead:
  !tops imms sec1 sec2.
    immutables_section_rel tops imms sec1 /\
    (!pre vis name ty slot post tv v.
       tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
       FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
       evaluate_type (type_env tops) ty = SOME tv) /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
         EL j sec2 = EL j sec1) ==>
    immutables_section_rel tops imms sec2
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build ctorDeployDeadSectionRelTheory` passes with zero failures, and `immutables_section_rel_dead` and every new helper have no CHEAT.
2. No duplicate or near-duplicate lemmas: search `lowering/**/*.sml` and `semantics/**/*.sml` before stating a new one, and reuse what exists. Existing `[local]` lemmas in other theories can't be reused or copied; prove what you need under a new name only if no exported lemma covers it.
3. No new axioms, no new premises on the frozen theorem, no changes to any definition, and no edits to existing files except `lowering/proofs/ctorDeployDeadSectionRelScript.sml`: nothing under `lowering/defs/`, `semantics/`, `venom/`, `frontend/`, and no edit to any other existing theory. Some ancestors are admitted locally with `cheat` in this worktree (uncommitted overlay edits); they are other runs' work. Don't touch or rely on their being cheats, and never stage them. Sibling helper theorems in `lowering/proofs/ctorDeployDead*Script.sml` other than yours may still be cheated (parallel runs); you may use their statements, but don't edit those files.
4. New helper lemmas go in `lowering/proofs/ctorDeployDeadSectionRelScript.sml` or in new theory files `lowering/proofs/ctorDeployDeadSectionRel*Script.sml`, added to `ctorDeployDeadSectionRel`'s `Ancestors`. Proofs stay under 50 lines each; give each case of an induction longer than 3 tactics its own lemma.
5. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. Every proof step must fit the default 2.5 s tactic timeout; no timeout changes.
6. Commits: stage files by name, only `.sml` files you created or edited under `lowering/proofs/` (and this TASK file); never `git add -u` or `-A`, since the overlay's edits to other files must not be committed. Never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*`, `alan-ref/`. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build ctorDeployDeadSectionRelTheory
```

## Background

- `immutables_section_rel tops imms sec` (`lowering/proofs/immutableSectionRelScript.sml`): the section holds every immutable's value: `val_in_memory tv v off sec` and `immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) sec)`, where `immutable_value_bytes_rel` compares only the bytes `immutable_value_mask` marks used.
- `imm_section_dead tops sec j` (`lowering/proofs/ctorDeployDefsScript.sml`): the bytes past each immutable's stored lengths, by `mem_dead_bytes` at the declared type `evaluate_type (type_env tops) ty`. The typing premise says each recorded `tv` is that declared type.
- The theorem says changing only those bytes keeps the relation. It is used by `deploy_venom_result_rel_dead` (`lowering/proofs/ctorDeployDeadScript.sml`, already proved from it).
- `mem_dead_bytes_range`, `mem_dead_bytes_frame` (`lowering/proofs/ctorDeployDeadSectionScript.sml`) are available; the frame lemma may still be cheated (parallel run).

## Domain Constraints

- Follow the definitions as they are; don't assume a narrower program subset than the premises give.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Relation | `lowering/proofs/immutableSectionRelScript.sml` | `immutables_section_rel`, `installed_code_rel` and lemmas |
| Masks, admissibility, encoding | `lowering/defs/immutableValueScript.sml, lowering/defs/immutableEncodingScript.sml` | `immutable_value_mask`, `immutable_mask_fit`, `immutable_value_bytes_rel`, `immutable_mask_same_bytes`, `immutable_value_admissible`, `encode_immutable_value` |
| Memory encoding | `lowering/defs/valueEncodingScript.sml` | `val_in_memory`, `mem_word_at`, `mem_bytes_at`, `type_memory_size` |
| Dead bytes | `lowering/proofs/ctorDeployDefsScript.sml` | `imm_section_dead`, `mem_dead_bytes` |
| Related immutable proofs | `lowering/proofs/immutableRelationScript.sml, lowering/proofs/immutableMemoryFrameScript.sml, lowering/proofs/immutableStagingBridgeScript.sml` | existing facts about values in sections and frames |
| Default values | `semantics/vyperValueScript.sml` | `default_value` |

## Notes

- Weakly frozen: helper lemmas you add may be restated freely; only the theorem above is frozen.

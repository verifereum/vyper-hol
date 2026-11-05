# TASK: Deploy piece Dead: load_contract records each immutable at its declared type (load_contract_immutables_typed)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (theorem in `lowering/proofs/ctorDeployDeadImmTypesScript.sml`, theory `ctorDeployDeadImmTypes`)

## Theorem Statement (FROZEN)

```sml
Theorem load_contract_immutables_typed:
  !tops am tx gobs am' rqs pre vis name ty slot post tv v.
    deploy_source_ok tops am tx /\
    load_contract NONE gobs am tx [(NONE, tops)] [] = INL (am', rqs) /\
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
    FLOOKUP (get_source_immutables NONE (account_immutables am' tx.target))
      name = SOME (tv,v) ==>
    evaluate_type (type_env tops) ty = SOME tv
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build ctorDeployDeadImmTypesTheory` passes with zero failures, and `load_contract_immutables_typed` and every new helper have no CHEAT.
2. No duplicate or near-duplicate lemmas: search `lowering/**/*.sml` and `semantics/**/*.sml` before stating a new one, and reuse what exists. Existing `[local]` lemmas in other theories can't be reused or copied; prove what you need under a new name only if no exported lemma covers it.
3. No new axioms, no new premises on the frozen theorem, no changes to any definition, and no edits to existing files except `lowering/proofs/ctorDeployDeadImmTypesScript.sml`: nothing under `lowering/defs/`, `semantics/`, `venom/`, `frontend/`, and no edit to any other existing theory. Some ancestors are admitted locally with `cheat` in this worktree (uncommitted overlay edits); they are other runs' work. Don't touch or rely on their being cheats, and never stage them. Sibling helper theorems in `lowering/proofs/ctorDeployDead*Script.sml` other than yours may still be cheated (parallel runs); you may use their statements, but don't edit those files.
4. New helper lemmas go in `lowering/proofs/ctorDeployDeadImmTypesScript.sml` or in new theory files `lowering/proofs/ctorDeployDeadImmTypes*Script.sml`, added to `ctorDeployDeadImmTypes`'s `Ancestors`. Proofs stay under 50 lines each; give each case of an induction longer than 3 tactics its own lemma.
5. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. Every proof step must fit the default 2.5 s tactic timeout; no timeout changes.
6. Commits: stage files by name, only `.sml` files you created or edited under `lowering/proofs/` (and this TASK file); never `git add -u` or `-A`, since the overlay's edits to other files must not be committed. Never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*`, `alan-ref/`. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build ctorDeployDeadImmTypesTheory
```

## Background

- After a successful deployment `load_contract NONE gobs am tx [(NONE, tops)] []`, the target's immutables (`account_immutables`, `lowering/e2eDefsScript.sml`) record each `Immutable` declaration `name : ty` of `tops` with type `evaluate_type (type_env tops) ty`.
- `load_contract_establishes_immutables_ready` (`semantics/prop/vyperTypeContractSoundnessScript.sml`) gives `immutables_ready` (`semantics/prop/vyperTypeInitialStateScript.sml`) for `check_contract F am'.layouts ...`'s artifact; `deploy_source_ok` (`lowering/proofs/ctorDeployDefsScript.sml`) includes `deploy_typing_ok` (`lowering/e2eDeployDefsScript.sml`), which has that `check_contract F` success. `load_contract_sources_layouts` (`lowering/proofs/ctorDeployDeadLoadScript.sml`, proved) gives `am'.sources`/`am'.layouts`.
- Missing pieces: the artifact's `cta_bare_globals` maps `(NONE, name)` to `ty` for each Immutable decl (built by `add_toplevel_static_maps`, `semantics/type/vyperTypeContractScript.sml`; names are unique by `check_contract`'s namespace checks), and `get_tenv` of the context is `type_env tops` (`get_tenv`, `type_env_all_modules`, `semantics/vyperContextScript.sml`).
- Consumer: `deploy_venom_result_rel_dead` (`lowering/proofs/ctorDeployDeadScript.sml`, already proved from it).

## Domain Constraints

- Follow the definitions as they are; don't assume a narrower program subset than the premises give.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Readiness after load | `semantics/prop/vyperTypeContractSoundnessScript.sml` | `load_contract_establishes_immutables_ready` and its clause lemmas |
| Readiness definition | `semantics/prop/vyperTypeInitialStateScript.sml` | `immutables_ready` |
| Checker | `semantics/type/vyperTypeContractScript.sml` | `check_contract`, `add_toplevel_static_maps`, `contract_namespaces_ok`, `toplevel_vtype_keys` |
| Contexts | `semantics/vyperContextScript.sml, semantics/vyperInterpreterScript.sml` | `get_tenv`, `type_env_all_modules`, `initial_evaluation_context`, `load_contract` |
| Deploy premises | `lowering/e2eDeployDefsScript.sml, lowering/proofs/ctorDeployDefsScript.sml` | `deploy_typing_ok`, `deploy_source_ok` |
| Load facts | `lowering/proofs/ctorDeployDeadLoadScript.sml` | `load_contract_sources_layouts` |

## Notes

- Weakly frozen: helper lemmas you add may be restated freely; only the theorem above is frozen.

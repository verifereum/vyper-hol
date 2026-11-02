# TASK: Repair creation-prelude supply preservation

## Meta
Status: planned
Created: 2026-11-02
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem account_supply_bound_create_prelude:
  account_supply_bound budget accounts /\
  value <= (lookup_account sender accounts).balance ==>
  account_supply_bound budget (create_prelude_accounts sender address value accounts)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All other existing theorem statements and executable definitions are frozen.

## Completion Criteria

- Replace the temporary admission in the theorem above with a checked proof.
- Build vyperExecutionSupplyTheory without new admissions, extra assumptions, or changed executable definitions.
- Retain only helpers consumed by the proof. Local proof helpers may be changed or removed.
- Commit only the affected script and this task file. Use the exact trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.
- Do not push, merge, rebase, squash, or edit unrelated files.

## Build

```sh
holbuild -j2 build vyperExecutionSupplyTheory
```

The owner runs final CI-mode checks separately. Keep the default tactic timeout.

## Background

The creation account prelude now clears the new address's storage. The prior supply proof fails after that definition change. This task repairs the proof without changing its domain or conclusion.

## Domain Constraints

- No new axioms, oracle use, retained cheats, or timeout overrides.
- No TRY/ORELSE around proof search.
- Use holbuild, never interactive proof-state tools or Holmake.
- Preserve all existing theorem statements and definitions in this theory.

## Available Resources

- semantics/prop/supply/evm/vyperExecutionSupplyScript.sml
- semantics/prop/vyperSupplyBoundaryScript.sml
- semantics/prop/vyperAccountSupplyScript.sml
- semantics/vyperCreateScript.sml
- .holbuild/src/verifereum/spec/vfmExecutionScript.sml
- .holbuild/src/verifereum/spec/prop/vfmExecutionPropScript.sml

## Notes

An independent read-only audit classified the frozen statement PROVABLE without a new premise. The analogous accounts_supply_create_prelude theorem was rebuilt successfully in this worktree. The original failed proof is retained in the source comment.

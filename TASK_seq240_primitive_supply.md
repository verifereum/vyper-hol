# TASK: Repair creation execution supply preservation

## Meta
Status: planned
Created: 2026-11-02
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem proceed_create_supply:
  execution_supply_bound budget st /\
  value <= (lookup_account sender st.rollback.accounts).balance ==>
  execution_supply_bound budget
    (SND (proceed_create sender address value code cappedGas st))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All other existing theorem statements and executable definitions are frozen.

## Completion Criteria

- Replace the temporary admission with a checked proof.
- Build vyperPrimitiveSupplyTheory without new admissions, extra assumptions, or changed executable definitions.
- Retain only helpers consumed by the proof. Local proof helpers may be changed or removed.
- Commit only the affected script and this task file. Use the exact trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.
- Do not push, merge, rebase, squash, or edit unrelated files.

## Build

```sh
holbuild -j2 build vyperPrimitiveSupplyTheory
```

The owner runs final CI-mode checks separately. Keep the default tactic timeout.

## Background

The creation execution now clears the new address's storage. The old proof establishes facts about the account map before this addition. Repair the proof without changing its domain or conclusion.

## Domain Constraints

- No new axioms, oracle use, retained cheats, or timeout overrides.
- No TRY/ORELSE around proof search.
- Use holbuild, never interactive proof-state tools or Holmake.
- Preserve all existing theorem statements and executable definitions.

## Available Resources

- semantics/prop/supply/evm/vyperPrimitiveSupplyScript.sml
- semantics/prop/supply/evm/vyperExecutionSupplyScript.sml
- semantics/prop/vyperSupplyBoundaryScript.sml
- semantics/vyperCreateScript.sml
- .holbuild/src/verifereum/spec/vfmExecutionScript.sml
- .holbuild/src/verifereum/spec/prop/vfmExecutionPropScript.sml

## Notes

The earlier account_supply_bound_create_prelude helper was repaired without changing its statement and passed an owner forced replay. The original failed proceed_create_supply proof is preserved in the source comment. The existing theory audit will reject any remaining admission.

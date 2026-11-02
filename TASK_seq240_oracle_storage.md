# TASK: Repair expression oracle-storage preservation proofs

## Meta
Status: planned
Created: 2026-11-02
Location: project root

## Theorem Statement (FROZEN)

The exact statement of `eval_expr_oracle_storage_mutual` in `lowering/exprOracleStoragePreservationScript.sml`, from `Theorem` to `Proof`, is frozen byte for byte. Its five meaningful projections already include `source_supply st`.

Do not modify this statement. Prove it as-is, or produce a counterexample.
All other existing theorem statements and executable definitions are frozen.

## Completion Criteria

- Repair the failing suspended RawRevert case and any subsequent failing proof cases of the same frozen mutual theorem.
- Remove the temporary admission and build exprOracleStoragePreservationTheory.
- Preserve the existing suspension/case coverage. Retain only proof helpers consumed by this theorem.
- No new admissions, hypotheses, axioms, or executable-definition changes.
- Commit only the affected theory and this task file. Use the exact trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.
- Do not push, merge, rebase, squash, or edit unrelated files.

## Build

```sh
holbuild -j2 build exprOracleStoragePreservationTheory
```

The owner runs final CI-mode checks separately. Keep the default tactic timeout.

## Background

The theorem is being migrated to a supply-bounded runtime domain. The current build fails in the RawRevert case after the lower source/runtime/storage theories built. Repair the proof while preserving the theorem's exact domain, conclusion, and all supported cases.

## Domain Constraints

- No new axioms, oracle use, retained cheats, or timeout overrides.
- No TRY/ORELSE around proof search.
- Use holbuild, never interactive proof-state tools or Holmake.
- Preserve every existing theorem statement and executable definition.
- Existing imported admissions outside this theory are acceptable dependencies; add none.

## Available Resources

- lowering/exprOracleStoragePreservationScript.sml
- lowering/exprOracleStorageInterfacesScript.sml
- semantics/prop/vyperOracleCallStorageScript.sml
- semantics/prop/vyperTypeEvalStoragePreservationScript.sml
- semantics/prop/vyperTypeEvalSoundnessScript.sml
- semantics/prop/supply/source/vyperSourceSupplyLib.sml
- semantics/prop/supply/source/vyperSourceSupplyScript.sml
- semantics/vyperInterpreterScript.sml
- .holbuild/logs/current/vyper-hol/exprOracleStoragePreservationTheory/build.log

## Notes

The original failing RawRevert proof is preserved in a source comment. No new semantic behavior is requested. An existing local tactic adapter forwards supply facts before storage simplification and rule application. All public interfaces stay frozen.

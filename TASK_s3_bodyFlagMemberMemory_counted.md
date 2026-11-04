# TASK: Counted body memory producer: compile_flag_member_body_sim_mem

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyFlagMemberMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_flag_member_body_sim_mem:
  !ctx func cenv cx env ty ann nsid mid es.
    expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
    expr_sim_mem ctx func cenv cx ty (FlagMember ann nsid mid) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Migrate this existing root to actual mode-T counted memory execution, preserving
its exact statement and full canonical posts. Preserve the old successful proof
as a comment when replacing it. Build bodyFlagMemberMemoryTheory with every existing strict
kernel gate intact. Keep every other existing public statement unchanged.

## Build

`holbuild -j2 build bodyFlagMemberMemoryTheory`

The old proof is not checked under the current counted schema. Independent
structural audit: PROVABLE unchanged for this gas-independent source action.
The existing proof currently supplies only an ordinary continuation fragment;
that is not sufficient evidence for an actual counted target path.

## Background

Shared memory judgments now quantify arbitrary source gas tails and require the
actual target path in mode T, full expression posts, allocation history/frontier
and continuing/terminal behavior. Source-only helpers and the generic stack/value
adapters have canonical checked owners. The general forcing/Bop/storage-copy
producers are independently owned and must not be changed here. These existing
leaf roots are concrete dependencies of the unfinished universal body proof.

## Domain Constraints

Only edit lowering/bodyFlagMemberMemoryScript.sml and its direct imports. No shared judgment,
source/compiler executable definition, new axiom/admission, strengthened premise,
weakened post, TRY/ORELSE search, tactic timeout override, cache/checkpoint bypass,
force rebuild or holbuild run/repl. Keep the complete full-state/body memory
precondition and all gas tails. No ordinary-to-counted path converse or theorem
that assumes the desired footprint. Reuse existing canonical facts; do not
reintroduce general forcing imports or duplicate helper families.

## Available Resources

- lowering/exprSimSourceScript.sml and exprSimHypsDefsScript.sml.
- lowering/exprSimMemoryStackScript.sml and exprSimMemoryValuesScript.sml.
- lowering/exprSimMemDefsScript.sml, bodyMemoryDefsScript.sml.
- lowering/fragGasPathMemScript.sml and fragGasSeqMemScript.sml.
- lowering/bodyLiteralMemoryScript.sml: independently checked counted constant.
- lowering/exprSimPropsScript.sml: source and post helper owner.
- lowering/exprSimCalldataScript.sml and exprSimNameWordScript.sml.
- lowering/emitHelperPropsScript.sml and venom/proofs/instMemFrontierScript.sml.

## Notes

Build logs are under .holbuild/logs/current/vyper-hol/bodyFlagMemberMemoryTheory/.
No public Theory.txt index is generated; preserve the strict load-time theorem
gates and inspect the successful build log for kernel evidence. Universal body
and S3 integration remain separate unfinished work.

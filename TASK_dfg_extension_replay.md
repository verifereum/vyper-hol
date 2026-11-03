# TASK: Bound the existing DFG environment-extension soundness proof

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem dfg_sound_fresh_untracked_extension:
  !dfg env env'.
    dfg_sound dfg env /\
    (!x. x IN FDOM env ==> FLOOKUP env' x = FLOOKUP env x) /\
    (!v dinst. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env' /\ dfg_tracked_opcode dinst.inst_opcode ==>
       v IN FDOM env) /\
    (!v dinst u. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env)
    ==>
    dfg_sound dfg env'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the actual default-limit failure in the existing proof, preserving the exact statement.
- Build dfgSoundStepTheory at the default tactic limit without new admissions.
- Keep all existing definitions, other theorem statements and unrelated proof bodies unchanged.

## Build

`holbuild -j2 build dfgSoundStepTheory`

## Background

Forced default replay stopped at the final compare-clause metis_tac[listTheory.MEM] step. This is a prerequisite for GAS same-list pass validation. An independent complete-statement audit checked all four component predicates and their tracked-opcode and operand-closure producers and found PROVABLE without any amendment. The original proof is retained.

## Domain Constraints

- Edit only the named proof body and necessary local helper theorems in its theory.
- No definitions, axioms, admissions, stronger assumptions, opcode exclusions or changes to executable semantics.
- Preserve all previously completed GAS, remap, CFG and DRET work.
- Use the default 2.5-second tactic limit; no timeout override and no TRY/ORELSE/FIRST around proof search.
- Report a different prerequisite root before expanding scope; do not edit shared tactics or other proofs speculatively.
- Commit substantive source only, excluding generated records. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/assert_elim/proofs/dfgSoundStepScript.sml: target proof, tracked-opcode predicate and existing extension helpers.
- venom/analysis/variable_range/proofs/rangeAnalysisProofsScript.sml: dfg_sound and its four component predicates.
- venom/analysis/dfg/defs/dfgDefsScript.sml: DFG lookup definitions.
- Existing finite_map and list ancestors supply lookup/domain and operand-membership facts.

## Notes

The exact statement parsed in the forced failing build. The owner checks the independent statement audit before launch, then checks schemas, forced default/CI replay and dependency tags after return.

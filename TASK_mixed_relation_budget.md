# TASK: Bound the mixed state-relation validity proof

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: venom/simulation/proofs

## Theorem Statement (FROZEN)
```sml
Theorem valid_state_rel_mixed_proof:
  !vars vars'. vars SUBSET vars' ==>
    valid_state_rel (state_equiv vars) (execution_equiv vars')
```
Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria
- Prove the unchanged complete mixed relation theorem at the default 2.5s step limit.
- Build execEquivParamProofsTheory without new admissions, axioms, premises or definition changes.
- Preserve all existing theorem statements and proofs outside the named root, except a necessary already-existing helper export or genuinely consumed proof helper.

## Build
holbuild -j4 build execEquivParamProofsTheory

## Background
The original proof's broad simplification of the full relation definition timed out twice at the default step limit. The statement already parses and the failed-prefix checkpoint reaches this exact theorem. This is a proof performance repair; the GAS oracle state and all semantics remain unchanged.

## Domain Constraints
Only venom/simulation/proofs/execEquivParamProofsScript.sml and prover task state may change. The frozen theorem statement stays byte for byte. Search for existing facts before adding any helper, including local copies. Reuse or export existing facts instead of duplicating them. No TRY/ORELSE around search, no timeout override, no new cheat or axiom, no executable-definition changes. Prove the whole statement, including every valid_state_rel conjunct.

## Available Resources
- venom/simulation/proofs/execEquivParamProofsScript.sml
- venom/simulation/proofs/execEquivParamBaseScript.sml
- venom/defs/stateEquivScript.sml
- venom/defs/stateFrameScript.sml
- venom/simulation/passSimulationPropsScript.sml
- venom/passes/assert_combiner/proofs/acChainProofsScript.sml

## Notes
No concurrent build or proof job in this worktree. Independent audit is recorded by the owner before launch. Existing proof remains intact.

# TASK: Bound existing immutable memory and pure binary error replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem immutable_op_mem_preserved[local]:
  !inst s v. is_immutable_op inst.inst_opcode /\
             inst.inst_opcode <> ISTORE /\
             step_inst_base inst s = OK v ==>
             v.vs_memory = s.vs_memory

Theorem exec_pure2_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_pure2 f inst s1 = Error err ==>
    ?err'. exec_pure2 f inst s2 = Error err'
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

- Repair the observed default-limit failures in these two existing proofs, preserving every existing schema and definition.
- Build allocaRemapProofsTheory at the default tactic limit, with no new admissions.
- Preserve shared tactics, unrelated proof bodies and every completed remap repair including MCOPY.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

MCOPY task at 6cca74aa3 fixed its actual dispatch failure and then stopped. Two distinct existing proofs have now exceeded the default2.5-second limit during replay: immutable_op_mem_preserved at rpt(CASE_TAC >> simp[]) and exec_pure2_error_transfer at exec_err_tac exec_pure2_def. Both complete exact schemas were independently checked against their current definitions and found PROVABLE, including all arity/error/output cases and arbitrary f. No statement or semantic change is needed. Existing proofs are retained.

This is a new isolated task. The earlier MCOPY task is stopped, and its generated PLAN/STATE must not be edited or reused for this new scope.

## Domain Constraints

- Edit only these two proof bodies plus necessary local helpers in venom/passes/shared/proofs/allocaRemapProofsScript.sml.
- Every existing definition, theorem statement, shared tactic, unrelated proof body and completed repair is frozen.
- No new definition, axiom, admission, assumption, opcode exclusion or executable/source semantic change.
- Default2.5-second step limit; no timeout override or TRY/ORELSE/FIRST around search.
- Report any newly failing outside-scope root before editing it; no blind unchanged retries.
- Commit substantive source only, leaving generated records untracked. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomInstScript.sml
- venom/proofs/venomInstProofs3Script.sml
- venom/passes/shared/proofs/passSharedFieldScript.sml

## Notes

The existing schemas have parsed and were built previously, but fresh replay exposed tactic-budget failures. Owner independently audits the frozen schemas and diff and performs forced default/CI replay and public dependency checks after return; these owner-only checks are not additional Alan completion gates.

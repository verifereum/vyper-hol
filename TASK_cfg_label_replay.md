# TASK: Replay non-jump label substitution within the default tactic limit

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_base_subst_label_non_jump[local]:
  !inst s old_lbl new_lbl.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\ inst.inst_opcode <> INVOKE /\
    FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl ==>
    step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
    step_inst_base inst s
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing proof without changing any existing theorem statement or definition.
- Retain the existing proof code and all other proven results.
- Build cfgNormBaseTheory at the default tactic limit.

## Build

`holbuild -j2 build cfgNormBaseTheory`

## Background

A forced preserving-pass replay reached the existing statement, then timed out after 2.5 seconds inside subst_label_nonjump_tac on the RETURN case. The exact statement independently audited PROVABLE against all relevant opcode and operand definitions, including undefined labels and DRET shape parsing. This is a proof-performance repair, not a semantics migration or a theorem restatement.

## Domain Constraints

- Edit only the proof of step_inst_base_subst_label_non_jump, its exclusive subst_label_nonjump_tac, and necessary proof helper theorems in venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml.
- All existing theorem statements and definitions are frozen. Add no definitions, admissions, axioms, assumptions, opcode restrictions, or timeout overrides.
- Keep the default 2.5-second tactic limit. No TRY/ORELSE/FIRST around proof search.
- Report any other prerequisite failure before broadening scope.
- Commit only substantive source changes; leave TASK/PLAN/DOSSIER and other prover working records alone. Do not add generated working records to git.
- End each commit message with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- `venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml`
- `venom/defs/cfgTransformScript.sml`
- `venom/defs/venomInstScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/defs/dretShapeDefsScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`

## Notes

The preflight build parsed this exact existing statement and failed within its proof; the original proof is retained. An independent read-only audit verified all listed resource paths and classified the exact statement PROVABLE. The owner performs forced default/CI replay and dependency checks after return.

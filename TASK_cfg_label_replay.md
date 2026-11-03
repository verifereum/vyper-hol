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
Triviality step_inst_base_non_jump_terminator_prev_bb:
  !inst (s:venom_state) p.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
```

Do not modify these statements. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing proof without changing any existing theorem statement or definition.
- Retain the existing proof code and all other proven results.
- Build cfgNormBaseTheory at the default tactic limit.

## Build

`holbuild -j2 build cfgNormBaseTheory`

## Background

A forced preserving-pass replay reached the existing statement, then timed out after 2.5 seconds inside subst_label_nonjump_tac on the RETURN case. The exact statement independently audited PROVABLE against all relevant opcode and operand definitions, including undefined labels and DRET shape parsing. This is a proof-performance repair, not a semantics migration or a theorem restatement.

## Domain Constraints

- Edit only the proofs of step_inst_base_subst_label_non_jump and step_inst_base_non_jump_terminator_prev_bb, their exclusive subst_label_nonjump_tac / nonjump_term_prev_bb_tac / dret_prev_bb_tac, and necessary proof helper theorems in venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml.
- All existing theorem statements and definitions are frozen. Add no definitions, admissions, axioms, assumptions, opcode restrictions, or timeout overrides.
- Keep the default 2.5-second tactic limit. No TRY/ORELSE/FIRST around proof search.
- Report any other prerequisite failure before broadening scope.
- Commit only substantive source changes; leave TASK/PLAN/DOSSIER and other prover working records alone. Do not add generated working records to git.
- End each commit message with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- `venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml`
- `venom/defs/cfgTransformScript.sml`
- `venom/passes/cfg_normalization/proofs/prevBbIndepScript.sml`
- `venom/defs/venomInstScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/defs/dretShapeDefsScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`

## Notes

The preflight build parsed this exact existing statement and failed within its proof; the original proof is retained. An independent read-only audit verified all listed resource paths and classified the exact statement PROVABLE. The owner performs forced default/CI replay and dependency checks after return.

The original label repair returned and is retained. Fresh whole-theory replay then stopped earlier in the unchanged step_inst_base_non_jump_terminator_prev_bb proof, inside a TRY-wrapped nonjump_term_prev_bb_tac on RET. The owner now permits a proof-only repair of that exact second frozen local result and its exclusive tactics. An independent read-only audit classified it PROVABLE on 0cbd9b6ff; every other definition, theorem statement and proof remains frozen.

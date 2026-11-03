# TASK: Replay the non-jump terminator predecessor-field proof

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Triviality step_inst_base_non_jump_terminator_prev_bb:
  !inst (s:venom_state) p.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing local proof without changing any definition or existing theorem statement.
- Build cfgNormBaseTheory at the default tactic limit.
- Preserve the completed label-substitution repair and all other existing proofs.

## Build

`holbuild -j2 build cfgNormBaseTheory`

## Background

Forced whole-theory replay reached this exact existing statement and timed out at 2.5 seconds inside TRY-wrapped nonjump_term_prev_bb_tac on RET. The exact statement independently audited PROVABLE against operand evaluation, all result constructors, DRET parsing/packing and the actual terminator table. The existing proof is retained. The earlier label-substitution repair is complete and is not this new task's scope.

## Domain Constraints

- Edit only the proof of step_inst_base_non_jump_terminator_prev_bb, its exclusive nonjump_term_prev_bb_tac / dret_prev_bb_tac, and necessary proof helper theorems in venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml.
- All definitions and existing statements are frozen, including Triviality declarations. Do not modify subst_label_nonjump_tac or the completed label proof.
- No new definition, admission, axiom, assumption, opcode restriction, or timeout override. Keep the default 2.5-second limit and no TRY/ORELSE/FIRST around search.
- Report another prerequisite failure before expanding scope.
- Commit only substantive source edits; leave TASK/PLAN/DOSSIER and other prover working records unchanged or untracked. Never add generated working records to git.
- End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- `venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml`
- `venom/passes/cfg_normalization/proofs/prevBbIndepScript.sml`
- `venom/defs/venomInstScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/defs/dretShapeDefsScript.sml`

## Notes

The statement has already parsed in owner forced replay. Independent audit classified it PROVABLE at 0cbd9b6ff; only task preparation changed afterward. All six resource paths were checked. The owner performs forced default/CI replay and dependency checks after return. This new prerequisite is isolated from the completed label task; its prior proof remains intact.

# TASK: Bound CFG return previous-block replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_base_ret_prev_bb[local]:
  !inst (s:venom_state) p. inst.inst_opcode = RET ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)

Theorem step_inst_base_retfmp_prev_bb[local]:
  !inst (s:venom_state) p. inst.inst_opcode = RETFMP ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing RET and matching RETFMP helper proof bodies without changing either statement.
- Build cfgNormBaseTheory with the default tactic limit and no new admissions.
- Preserve all definitions, previously completed CFG repairs, shared tactics and unrelated proof bodies.

## Build

`holbuild -j2 build cfgNormBaseTheory`

## Background

A fresh forced preserving-target replay stopped at RET's broad step_inst_base simplification after an earlier whole-theory replay had passed. RETFMP uses the identical repeated proof pattern. An independent audit checked both complete statements against all operand arities, malformed operands, return records and gas streams: both are provable as stated.

## Domain Constraints

- Scope: only the two named proof bodies and necessary local helpers in venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml.
- No executable or proof definitions, changed statements, assumptions, axioms, admissions, timeout overrides or TRY/ORELSE/FIRST around proof search.
- Keep default 2.5-second tactic limit. Preserve every other proof body and the checked GAS/remap/DFG/effect-free work.
- Report another prerequisite root before expanding scope; no speculative cleanup.
- Commit substantive source only, leave generated task records untracked. End each commit message with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/cfg_normalization/proofs/cfgNormBaseScript.sml: exact roots and local eval_operands_prev_bb/result-map interface.
- venom/defs/venomExecSemanticsScript.sml: step_inst_base, step_inst_base_opcode_eqs and step_inst_base_RETFMP.
- venom/defs/venomStateScript.sml: previous-block state updates and operand evaluation.
- venom/defs/venomInstScript.sml: instruction and opcode accessors.

## Notes

Actual default-limit failure: step_inst_base_ret_prev_bb at simp[step_inst_base_def, eval_operands_prev_bb], line2814. Both exact statements have already parsed; no existing proof is replaced with a placeholder. Owner checks exact schemas, complete default/CI forced replay and public dependency tags after return.

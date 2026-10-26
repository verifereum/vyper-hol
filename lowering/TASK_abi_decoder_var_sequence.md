# TASK: Keep decoder variable-extension proofs within the tactic timeout

## Meta

Status: planned
Priority: P1
Location: lowering/abiDecoderVarSequenceScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem abi_decoder_step_inputs_defined:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK u ==>
  abi_decoder_inputs_defined inst s
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All other existing theorem statements and definitions are also frozen.

## Completion Criteria

- The target theory builds with no new admissions, axioms or kernel oracles.
- The frozen theorem and existing downstream theorems all build at the
  default 2.5-second per-step timeout.
- Preserve the original proof code if a temporary admission is ever needed;
  leave no temporary admissions in the completed work.
- No changed source semantics, opcode list, hypotheses or definitions.
- If the theorem is false, produce a concrete HOL counterexample rather than
  changing its statement.

## Build

```sh
holbuild --max-heap 7000 -j2 build abiDecoderVarSequenceTheory
```

Run from the project root. Build only affected theories. Validate shared
helper machinery before using it in the main proof.

## Background

The target theorem already parses, but its original final tactic exceeds
the default step timeout. It is a dependency of the encoder fragment bridge.
This task repairs proof execution without changing any contract.

## Domain Constraints

- Use holbuild, no interactive HOL or Holmake.
- Never raise or disable the tactic timeout.
- Never wrap proof search in TRY or ORELSE.
- Existing proved statements and definitions are frozen.
- Do not use unrelated admitted correctness results.
- Commit milestones with trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/abiDecoderVarSequenceScript.sml`: target and downstream results.
- `lowering/abiDecoderVarExtendScript.sml`: variable-extension properties.
- `venom/defs/venomExecSemanticsScript.sml`: instruction semantics (locate
  the actual path using the repository file index if layout differs).
- `lowering/emitHelperPropsScript.sml`: small instruction execution facts.
- `lowering/defs/compileEnvScript.sml`: state and freshness definitions.

## Notes

The existing proof failed at
`gvs[Once step_inst_base_def, exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def, AllCaseEqs(), eval_operand_def]`.
Splitting the rewrite list still timed out in `gvs[Once step_inst_base_def]`.
Unfolding that assumption followed by `asm_simp_tac bool_ss []` also timed
out. All attempts preserved the statement; the original proof is restored.

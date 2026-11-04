# TASK: Bound the emitted instruction prefix proof

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem exec_block_inst_seq_prefix:
  ∀ insts fuel ctx bb idx ss ss'.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀ k. k < LENGTH insts ⇒
          get_instruction bb (idx + k) = SOME (EL k insts))
    ⇒
    exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
      exec_block fuel ctx bb (ss' with vs_inst_idx := idx + LENGTH insts)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

All existing statements, definitions, ML tactics, other proof bodies and files
are frozen at b5a885eb6. Change only this root's proof and necessary consumed
local helpers in its defining script. Retain its existing proof until replacing
it. This task covers one independent root, not the other emission lemmas.

## Completion Criteria

1. The complete unchanged root builds at the default step limit without new
   admissions or CHEAT warnings.
2. All other schemas, definitions, proof bodies, ML tactics and files stay unchanged.
3. Report the actual named-target build result and any later failure without
   expanding scope. The owner performs one cached default checkpoint-free check
   and checks public admission dependencies after return.

## Build

```sh
holbuild -j2 build emitHelperPropsTheory
```

## Background

The full statement parses and has an existing proof. The initial focused
consumer build timed out at a later MCOPY dispatch. Its single permitted
unchanged-theory rerun stopped earlier at this root's simp_tac(srw_ss())[]
following the index-zero lookup. No source definition or theorem statement
may change. Independent whole-schema audit classified the unchanged root
PROVABLE, including arbitrary fuel/cursor, malformed operands, all result
constructors and exact preservation of gas/readings and all other fields.
The final O1 call proof in e2eCorrectnessScript.sml is unrelated
and frozen throughout this task.

## Domain Constraints

- Preserve the complete frozen schema and every other existing proof.
- No new cheat, axiom, hypothesis, restricted subset or opaque fact.
- Default 2.5s limit; never raise it, disable checks or catch timeouts.
- No TRY/ORELSE/FIRST around search; select goals explicitly.
- Use holbuild only; no interactive HOL, Holmake, run/repl or explicit theory loads.
- Reuse existing facts before adding necessary consumed local helpers.
- Report later failures without expanding scope or resuming a completed task.
- Commit only substantive source edits; leave Alan working files untracked.
  End commits with `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/emitHelperPropsScript.sml`: frozen root, adjacent sequence and emission lemmas.
- `lowering/defs/emitHelperScript.sml`: emission definitions.
- `lowering/exprLoweringPropsScript.sml`: run_inst_seq and existing lowering execution facts.
- `venom/simulation/proofs/instIdxIndepScript.sml`: instruction-index independence.
- `venom/defs/venomExecSemanticsScript.sml`: actual block, instruction, executor and call semantics.
- `venom/defs/venomStateScript.sml`: complete Venom state including gas readings.
- `venom/defs/venomInstScript.sml`: instruction/opcode/terminator definitions.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: proof-control conventions.

## Notes

The owner will compare every frozen schema and byte outside the permitted
proof/helper area. The larger current-D consumer check is unfinished.

# TASK: Count the actually executed prefix of an aborting instruction sequence

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/fragGasSeqAbortScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem run_inst_seq_abort_gas_path:
  !memory code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    (memory ==> run_inst_seq_mem_ok code s) /\
    run_inst_seq code s = Abort a t ==>
    ?n j. gas_marked_path memory ctx func s n
      (Abort a (t with vs_inst_idx := j))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build fragGasSeqAbortTheory` passes with the frozen root.
2. No new admission, axiom, definition, timeout override, or TRY/ORELSE around proof search. Preserve all existing statements and definitions.
3. The path must be actual execution, with the complete abort state preserved except its instruction index. Both ordinary and memory modes must work. Target GAS instructions are allowed and counted along the actual executed prefix.
4. Reuse existing generic execution and counted-path lemmas rather than duplicate them. No lets in new theorem statements. Commit only task-owned SML files, with trailer `Bot: sol (OpenAI GPT-6.1 Sol (Codex))`.

## Build

```sh
holbuild -j2 build fragGasSeqAbortTheory
```

## Background

Unary arithmetic and conversion fragments can terminate at a failing ASSERT. Their successful instruction-sequence paths already have counted execution lemmas; the same consumers need a concrete terminal path. The arbitrary final index is intentional: the complete abort state otherwise agrees with the sequential evaluator, and expression exit judgments do not observe that index.

## Domain Constraints

Only the counted terminal-sequence proof and necessary reusable proof helpers are in scope. Do not alter source or target semantics, opcode classification, oracle policies, gas counting, memory safety, postconditions, or any existing theorem. An early abort does not execute the remainder of the list.

## Available Resources

- lowering/fragGasSeqAbortScript.sml: frozen root and initial proof attempt.
- lowering/fragGasSeqScript.sml: successful ordinary sequence path.
- lowering/fragGasSeqMemScript.sml: successful memory sequence path and single-step boundary.
- lowering/fragGasModeScript.sml: shared mode-indexed actual path.
- lowering/fragGasPathScript.sml, lowering/fragGasPathMemScript.sml: edge and path definitions and composition.
- lowering/fragExecScript.sml, lowering/fragExecMemScript.sml: sequential execution, abort and index-frame facts.
- lowering/exprLoweringPropsScript.sml: sequential instruction evaluator.
- lowering/stmtSimPropsScript.sml: existing concrete emitted-abort path.
- venom/defs/venomExecSemanticsScript.sml: actual instruction semantics.

## Notes

Build 69581 parsed the exact root and built its current ancestors, then the initial proof left the expected ordinary and memory path goals. Independent audit classifies the root PROVABLE with no premise gap and found no existing generic counted abort-prefix theorem to duplicate. No theorem is claimed built yet.

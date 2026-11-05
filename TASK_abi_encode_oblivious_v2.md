# TASK: lower_abi_encode is oblivious to its entry block

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimAbiEncodeObliviousScript.sml

## Theorem Statements (FROZEN)

```sml
Theorem lower_abi_encode_start_oblivious:
  !ensure mid src info maxlen.
    frag_start_oblivious (lower_abi_encode ensure mid src info maxlen)

Theorem lower_abi_encode_frag_facts:
  !ensure mid src info maxlen sa out sb.
    lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
    (!l. src <> Label l) ==>
    cs_extends sa sb /\ frag_ops_free sa sb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    (sa.cs_blocks = sb.cs_blocks ==> frag_gas_free sa sb)
```

Do not modify these statements, nor the definitions they use (`frag_start_oblivious_def`, `start_relabel_def`, `start_swap_def`, `frag_ops_free_def`, `frag_code_def`, `frag_gas_free_def` in `lowering/exprSimAbiGasBridgeScript.sml`). Prove them as-is, or produce a counterexample.

## Completion Criteria

- Both theorems proved with no `cheat` in `lowering/exprSimAbiEncodeObliviousScript.sml`, or in new helper theories named `exprSimAbiEncodeOblivious<Part>`. The leaf's `Ancestors` may change.
- No new axioms or admissions. Definitions only as proof-only helpers.
- `holbuild -j4 build exprSimAbiEncodeObliviousTheory` passes at the default step limit.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

```sh
holbuild -j4 build exprSimAbiEncodeObliviousTheory
```

Default tactic timeout and memory limits. Many ancestor theories are admitted by a local overlay (cheated in the work tree, skip-worktree); inherited admissions from them are expected. Do not edit, commit or un-skip those files. The relabeled bridge theorems in `exprSimAbiGasBridge` are admitted here (another job proves them); this task only uses its definitions.

## Background

A previous run refuted the facts lemma without the `src` premise: with `src = Label sa.cs_current_bb` and no blocks emitted, the encoder's `MLOAD [src]` breaks `frag_gas_free`. The premise excludes that; the case's `src` is always a `Var`.

`lower_abi_encode` (`lowering/defs/builtinAbiScript.sml`) is a compile-monad program: `compile_alloc_buffer`, `emit_op`/`emit_void`, and `compile_abi_encode_to_buf` (`lowering/defs/abiEncoderScript.sml`, recursive over the ABI encoding info, with loops that open blocks through `new_block` and fresh labels).

Obliviousness. The compile primitives (`compileEnvScript.sml`: `emit`, `fresh_var`, `fresh_id`, `fresh_label`, `new_block`) never read `cs_current_bb` or the IDs of `cs_current_insts`, with two exceptions to watch:
- `new_block` returns the old `cs_current_bb`. A program that discards that result is oblivious; one that uses it in emitted code is not. Find whether the encoder uses it.
- `block_is_terminated` reads the opcode of the last current instruction, and `start_relabel` replaces the pre-fragment instructions with NOPs. The encoder never calls it: only `emit_jmp_if_not_terminated` (`emitHelper`) does, and that is used only by statement and module lowering.

A direct induction on single primitives won't work, since `start_swap` describes the end state relative to the start. The natural route is a more general invariant over the compile monad, e.g. "running from `start_relabel L ids sa` gives the same result and the end state related to the original by renaming the entry block's label (in `cs_current_bb` while the entry block is open, else in that one finished block) and replacing its pre-fragment prefix". Prove that invariant for the primitives and the monad's bind/return/case/if, then for `compile_abi_encode_to_buf` by its recursion, and conclude.

Facts.
- `ALL_DISTINCT` IDs: every emitted instruction gets its ID from `fresh_id`, strictly increasing `cs_next_id`.
- `~MEM sb.cs_current_bb (FRONT labels)`: every label opened by `new_block` comes from `fresh_label` at strictly increasing `cs_next_label`. `fresh_label_output` is injective: the part after the last `_` is `toString k`, which has no `_`. The labels in `FRONT (emitted_blocks sa sb)` were opened before the last `new_block`, which opened `sb.cs_current_bb`.
- With no blocks emitted, `frag_gas_free`'s label conjuncts hold if the emitted code has no `Label` operands.
- `frag_ops_free`: the encoder emits no GAS, INVOKE, PHI, STOP or RETURN.

Earlier work on the case branch may help: `lowering/exprSimAbiEncodeLabelProvenanceScript.sml` (label provenance of the recursive encoder) and `lowering/abiEncoderFragmentScript.sml`, `lowering/abiEncoderPropsScript.sml`.

## Domain Constraints

- Don't change existing theories; helpers go in this leaf or new `exprSimAbiEncodeOblivious<Part>` theories.
- No TRY/ORELSE around proof search, no timeout overrides, no unsafe tactics.

# TASK: MakeSSA block shape (where each input instruction lands)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/make_ssa/proofs/makeSsaCurrentLockstepShapeScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The two cheated theorems in `venom/passes/make_ssa/proofs/makeSsaCurrentLockstepShapeScript.sml`:

```sml
Theorem make_ssa_current_fn_block_shape:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?bb'. lookup_block l fn'.fn_blocks = SOME bb' /\
    LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
    phi_prefix_length bb'.bb_instructions <=
      phi_prefix_length bb.bb_instructions +
      (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions) /\
    (!j. phi_prefix_length bb'.bb_instructions <= j /\
         j < phi_prefix_length bb.bb_instructions +
             (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions) ==>
         (EL j bb'.bb_instructions).inst_opcode = ASSIGN \/
         (EL j bb'.bb_instructions).inst_opcode = NOP) /\
    !k. phi_prefix_length bb.bb_instructions <= k /\
        k < LENGTH bb.bb_instructions ==>
        (EL (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
            bb'.bb_instructions).inst_opcode =
          (EL k bb.bb_instructions).inst_opcode /\
        (EL (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
            bb'.bb_instructions).inst_id =
          (EL k bb.bb_instructions).inst_id /\
        LENGTH (EL (k + (LENGTH bb'.bb_instructions -
                         LENGTH bb.bb_instructions))
                   bb'.bb_instructions).inst_outputs =
          LENGTH (EL k bb.bb_instructions).inst_outputs

Theorem make_ssa_current_fn_lookup_block_rev:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn'.fn_blocks = SOME bb' ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb
```

**Do not modify these statements, any definition they use, `makeSsaCurrentDefsScript.sml`, or any existing theory.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `makeSsaCurrentLockstepShapeTheory`.
2. Helper lemmas go in `makeSsaCurrentLockstepShapeScript.sml` or in new theories next to it under `venom/passes/make_ssa/proofs/`; each exists once, in its most general form. Reuse existing lemmas (e.g. `make_ssa_current_fn_labels`, `rename_current_block_insts_ids`, `rename_current_inst_id`, `update_current_succ_phis_labels`) rather than re-proving them.
3. No change to existing theories.

**If a theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild -j4 build makeSsaCurrentLockstepShapeTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

This fixes where MakeSSA puts each input instruction, for a later step-for-step simulation (`frame_lockstep` in `venom/compiler/o1FrameLockstepScript.sml`) whose position map is `k + (LENGTH out - LENGTH in)` per block. Only instructions from the input's first non-PHI on are stepped: a block's leading PHIs are evaluated together at block entry (`eval_phis`, `phi_prefix_length`), so the theorem says nothing about positions inside the input's PHI prefix. The output's extra leading positions that are not in its own PHI prefix must be ASSIGN or NOP (the copies the cleanup makes from collapsed PHIs).

`make_ssa_current_fn` inserts PHIs at block heads (`insert_phi_at_block` prepends), renames along the dominator tree (`rename_current_blocks`; outputs renamed, non-PHI operands renamed, PHI operands patched per predecessor by `update_current_succ_phis`), and only when the input had leading PHIs runs the cleanup (`simplify_current_phis_if`), which rearranges each block's leading PHI prefix into the PHIs that stay PHIs followed by the collapsed copies, and reassigns ids in the original order.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search. Never raise the tactic timeout (2.5 s per step).
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | make_ssa_current_fn, add_phi_nodes_supply, rename_current_blocks, update_current_succ_phis, simplify_current_phis_if and their parts |
| Legacy MakeSSA defs | `venom/passes/make_ssa/defs/makeSsaDefsScript.sml` | insert_phi_at_block, compute_defs, dom tree type |
| Current-variant lemmas | `venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml`, `makeSsaCurrentInductScript.sml`, `makeSsaCurrentCfgScript.sml` | labels preserved, inst ids, supply, dom-tree induction |
| Legacy proofs | `venom/passes/make_ssa/proofs/makeSsaHelperScript.sml`, `makeSsaProofScript.sml` | lookup_block/replace_block lemmas for the name-based variant |
| Block lookup | `venom/defs/` (grep `lookup_block_def`, `replace_block_def`) | lookup_block, replace_block |
| Semantics | `venom/defs/venomExecSemanticsScript.sml` | phi_prefix_length, eval_phis |
| Well-formedness | `venom/defs/venomWfScript.sml`, `venom/defs/cfgWfScript.sml` | wf_function (distinct labels), fn_inst_wf |
| Premise defs | `venom/compiler/o1PassContractScript.sml` (make_ssa_input_ok, first_block_no_phi), `venom/compiler/unitShapeDefsScript.sml` (first_block_no_preds), `venom/defs/irSupplyScript.sml` | |
| Consumer | `venom/passes/make_ssa/proofs/makeSsaCurrentLockstepScript.sml`, `venom/compiler/o1FrameLockstepScript.sml` | make_ssa_pos and frame_lockstep, for context only |

## Notes

- Not every premise is needed; they are the consumer's, given so you can use any of them.

# TASK: DFT's frame simulation (memory transport for the O1 contract)

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler/o1DftLiftScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem dft_frame_sim:
  !C C' L.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    EVERY fn_shape_ok C.ctx_functions /\ ctx_labels_bound C L ==>
    LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                       fn_entry_label fn' = fn_entry_label fn /\
                       frame_sim L C C' fn fn')
             C.ctx_functions C'.ctx_functions
```

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

Definitions it uses:
- `frame_sim_def`, `frame_reach`, `fn_entry_state`, `mem_corr`, `call_corr`: venom/compiler/o1PassLiftScript.sml.
- `dft_fn_rel_def`, `ctx_labels_bound_def`, and `dft_run_blocks_rel` (cheated, owned by another task; you may use it): venom/passes/dft/proofs/dftRunRelScript.sml.
- `dft_block_rel_def`, `dft_must_order_def`: venom/passes/dft/proofs/dftScheduleOrderScript.sml.
- `id_before_def`, `dft_fallible_order_kept_def`, `is_fallible_def`: venom/passes/dft/defs/dftDefsScript.sml.
- `fn_shape_ok_def`, `inst_shape_ok`, `label_positions_ok`: venom/compiler/unitShapeDefsScript.sml.

## Completion Criteria

1. `holbuild --max-heap 7000 -j4 build o1DftLiftTheory` passes with zero CHEAT warnings from o1DftLiftTheory and any helper theory you add. Other tasks own the cheats in dftRunRelTheory (`dft_run_blocks_rel`) and dftScheduleOrderTheory (`dft_fn_block_rel`); use those theorems freely and leave them alone.
2. No duplicate or near-duplicate lemmas.

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, do not weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build o1DftLiftTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

DFT reschedules each block's non-pseudo instructions (dft_block_rel): every pair ordered by dft_must_order keeps its order, and fallible instructions keep theirs (dft_fallible_order_kept, part of dft_fn_rel). frame_sim says that every state a frame of fn' reaches in C' (frame_reach) has a counterpart that the frame of fn reaches in C from the same entry state, related by mem_corr and call_corr. o1PassLift's frame_sim_mem_inv then carries the memory invariant from C to C'.

A statement checker (reading only) judged it provable. Its reasoning:
- vs_alloca_next, vs_allocas and vs_initial_fmp never change in a frame, because there's no ALLOCA and merge_callee_state keeps the caller's. So a C' state at an instruction with no memory ranges and no INVOKE matches any C state, e.g. the one at the block entry.
- For an instruction M in C' that has memory ranges, or is an INVOKE, C reaches the same M with the same operand values:
  - Every C instruction before M that can stop the run is also before M in C'. Roots (ASSERT, ASSERT_UNREACHABLE) come first by clause 4 of dft_must_order. RETURNDATACOPY and INVOKE conflict on effects. Terminators come last.
  - Non-fallible instructions don't error in a well-formed function. inst_wf covers arity; pseudos stay in the identical prefix; labels are bound (ctx_labels_bound); shape bans OFFSET, DJMP, CREATE, CREATE2, DELEGATECALL and SELFDESTRUCT.
  - Variables are defined: SSA def_available_at, plus a strict-dominator invariant like `strict_dom_vars_defined` (venom/passes/sccp/proofs/sccpCorrectnessProofsScript.sml:237).
  - Values are equal, because declared effects cover all hidden state read and written. Instruction ids are distinct, and SSA outputs are distinct.
- INVOKE: only var-only, effect-free instructions cross it, so execution_frame and arguments are equal. With the same fuel, dft_run_blocks_rel forces C's callee to return exactly what C' 's callee returns. The callee entry state from setup_callee has the entry label and labels L.

Likely needs a within-block commutation lemma (C' 's executed prefix against C's prefix up to M, effect by effect) plus the dominator invariant.

## Domain Constraints

- Build only with holbuild; no Holmake, no hol4-mcp, no interactive `g`/`e` sessions. Read the repo's `AGENTS.md`.
- No `cheat` in the result. Never raise the tactic timeout (2.5 s per step). No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Do not change existing definitions or proved theorems. Helpers go in this theory or new theories next to it (venom/compiler/ or venom/passes/dft/proofs/); no new axioms or hypotheses.
- Keep proofs short (≤ ~50 lines each). Use `--max-heap`, never `--maxheap`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Lift | venom/compiler/o1PassLiftScript.sml | frame_sim, frame_reach, mem_corr, call_corr, raw_reachable_labels, and the lift lemmas (see how other passes' frame_sim proofs go, e.g. venom/compiler/o1ContractSueScript.sml statements) |
| DFT relations | venom/passes/dft/proofs/dftScheduleOrderScript.sml, dftRunRelScript.sml, dftSsaPreserveScript.sml, dftIndexedExecScript.sml | dft_block_rel, dft_run_blocks_rel and its helpers (dft_fn_rel_lookup_function, dft_block_rel_lookup_block, ...), block correspondence lemmas |
| DFT commutation | venom/passes/dft/proofs/dftCommutation*, dftCorrectness*, dftPermSim* | existing instruction-commutation lemmas (check hypotheses) |
| Semantics | venom/defs/venomExecSemanticsScript.sml | step_inst, run_blocks, setup_callee, merge_callee_state |
| Effects | venom/defs/venomEffectsScript.sml | read_effects, write_effects, opcode_fail_class |
| Dominators | venom/defs/venomWfScript.sml, venom/passes/sccp/proofs/sccpCorrectnessProofsScript.sml | wf_ssa, def_available_at, strict_dom_vars_defined |
| Intuition | comment above the theorem | unchecked proof sketch |

## Notes

- Other alan runs are proving dft_run_blocks_rel and dft_fn_block_rel in parallel; their helper lemmas will be merged later. Don't edit their theories.

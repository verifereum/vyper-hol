# TASK: a planned block's code is placed at its label in the assembled program (dfs_block_code_placed)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnPlanPlaceScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem dfs_block_code_placed:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth lbl_ctr
   ps_end lbl bb ps_dfs block_ops ps_dfs_after.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      r.sr_spill_base lbl_ctr = SOME (r.sr_plan, ps_end) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth r.sr_spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after)
    ==>
    ?off pc.
      FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME pc /\
      asm_block_at prog pc (execute_plan cp.cp_initial_fmp block_ops) /\
      (!l j. j < LENGTH (execute_plan cp.cp_initial_fmp block_ops) /\
             EL j (execute_plan cp.cp_initial_fmp block_ops) = AsmLabel l ==>
             ?off'. FLOOKUP lo l = SOME off' /\ off' < dimword (:256) /\
                    FLOOKUP o2pc off' = SOME (pc + j))
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnPlanPlaceTheory` passes with no failure, and `dfs_block_code_placed` and any helper theory you add have no CHEAT.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

Scope: only `dfs_block_code_placed`. `fn_region_placed`, `revert_postamble_placed` (same theory) are other runs' work: leave their `cheat` alone and don't depend on them. Other cheated theorems in neighbouring theories (fnFrameSteps, fnFrameBoundary, fnPlanPlace, fnPlanLineage, venomToAsmProps) are other runs' work too.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (concrete terms, `EVAL`).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this directory>
holbuild --gcthreads 8 -j4 build fnPlanPlaceTheory
```

Always pass `--gcthreads 8` (a Poly/ML GC assertion fails without it on this host).

## Background

vyper-hol's Venom-to-EVM code generator plans each block's stack code and
lays the plans out with `codegen_assembly`. The block induction behind
`venomToAsmProps$gen_fn_frame_simulation` needs this theorem as one step.
The comment above the statement in `venom/codegen/proofs/fnPlanPlaceScript.sml` says where it is used and
why it should hold. A statement check found it provable as stated.

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit definitions in `venom/codegen/defs`, `venom/analysis` or `venom/defs`.
- Keep helpers in `venom/codegen/proofs/`, in a new `fnPlanPlaceDfsBlockScript.sml` that `fnPlanPlace` imports, so parallel runs on the same theory don't collide. Generalizing an existing lemma is fine if you add the general form as a new theorem and leave the old one in place; making an existing `[local]` lemma public is fine.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Placement facts | venom/codegen/defs/codegenScript.sml | `codegen_assembly`, `asm_symbols_ok`, `asm_symbols_ok_distinct` (distinct names, size bound) |
| Label offsets | venom/codegen/defs/symbolResolveScript.sml | `compute_label_offsets`, `build_offset_to_pc`, `asm_inst_size` |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_context_plan`, `context_plan_ops`, `revert_postamble`, `generate_fn_plan_with_cleanup_analyzed` |
| DFS states | venom/codegen/proofs/fnPlanLineageScript.sml, fnPlanCoverScript.sml | `dfs_block_state` and its coverage |
| Assembly | venom/codegen/defs/asmSemScript.sml, planExec | `asm_block_at`, `execute_plan` |

## Notes

- Other runs are proving the sibling theorems in parallel on other branches; don't rely on them.

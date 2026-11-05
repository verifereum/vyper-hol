# TASK: clean_stack_plan's cleanup against the frame invariant (clean_stack_plan_frame_sim)

## Meta
Status: planned
Priority: P0
Created: 2026-11-05
Location: venom/codegen/proofs/fnFrameCleanStackScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem clean_stack_plan_frame_sim:
  !ctx cp lo o2pc prog liveness cfg fn bb base ps vs as clean_ops ps2
   r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generated_plan_state_wf_marked base ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
           off < dimword (:256)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp clean_ops)
    ==>
    ?n as2.
      asm_steps lo o2pc prog n as = AsmOK as2 /\
      as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
      generated_plan_state_wf_marked base ps2 /\
      (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
            op = dead_stack_marker \/ MEM op ps.ps_stack \/
            op IN FDOM ps.ps_spilled)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build fnFrameCleanStackTheory` passes, with no CHEAT in fnFrameCleanStack or in any theory you add.
2. The statement above is byte-for-byte unchanged in `venom/codegen/proofs/fnFrameCleanStackScript.sml`.
3. No duplicate or near-duplicate lemmas: search before adding one; each helper exists once in its most general form.

**If the theorem is false as stated:** give a concrete counterexample (a planner state, a stack, the cleanup's code) and the tightest sufficient fix. Do NOT weaken the statement.

## Build

```
cd <this directory>
holbuild -j4 build fnFrameCleanStackTheory
```

## Background

The codegen proof (Venom IR to EVM assembly) simulates each block against the frame invariant `frameRel$fn_frame_inv`. A non-entry block with exactly one predecessor runs `clean_stack_plan` first: it pops variables the predecessor left that this block doesn't need (`popmany_plan`: swaps to the top, spilling when deeper than 16, then POP), or replaces them by `dead_stack_marker` without code. `cleanOpsSim$clean_ops_sim` proves this against the whole-stack relation `venom_asm_rel` for stacks of at most 17 entries; this theorem is the frame version for any depth, from a planner state that may already repeat `dead_stack_marker` (`fnPlanPrefix$generated_plan_state_wf_marked`). Its consumer, `fnFrameSinglePred$single_pred_prefix_frame_sim`, already uses it. The SML comment above the statement says why it should hold.

## Domain Constraints

- holbuild only. Never `holbuild run` or `holbuild repl`; probe with scratch lemmas ending in `cheat` and rebuild, and remove probes before finishing.
- Never raise the tactic timeout (no `--tactic-timeout`, no `tactic_timeout` in holproject.toml). A step over 2.5 s is a performance bug: split it.
- No `TRY`/`ORELSE` around metis or other proof search; select goals with `>~`, `>-`, `>|`.
- No `cheat` left anywhere, no new axioms, no `let` in theorem statements.
- Edit only `venom/codegen/proofs/fnFrameCleanStackScript.sml` and new leaf theories next to it (`venom/codegen/proofs/fnFrameCleanStack*Script.sml`, registered in holproject.toml's roots before `fnFrameCleanStackScript.sml`). Don't edit other theories (no `[local]` removals elsewhere); if a needed lemma is `[local]` elsewhere, re-derive it from exported results. Don't mark a helper `[local]` if other theories could use it.
- Don't touch `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, `venom/analysis/` or `venom/codegen/defs/`.
- Variable names that clash with constants (`cp`, `base`, `fn`, `s`) get primed by `gen_tac`; rename them. Use `rename1`/`qpat_x_assum`, never generated names.
- Commits: commit only scripts under `venom/codegen/proofs/` and holproject.toml (never `.alan/`, `PLAN_*`, `STATE_*`, `LOG_*`, `LEARNINGS_*`, `DOSSIER_*`, this task file or tool outputs). End every commit message with these two lines:
  `Bot: opus (Claude Opus 5.5)` and `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target | venom/codegen/proofs/fnFrameCleanStackScript.sml | statement + intuition comment |
| Consumer | venom/codegen/proofs/fnFrameSinglePredScript.sml | `single_pred_prefix_frame_sim` uses it (glue proof already written) |
| Join sibling | venom/codegen/proofs/fnFrameStepsScript.sml | `phi_prefix_frame_sim` (same conclusion shape) |
| Prefix planner | venom/codegen/proofs/fnPlanPrefixScript.sml | `generate_block_insts_prefix_def`, `generate_block_insts_plan_split`, `generated_plan_state_wf_marked_def`, `generated_plan_state_wf_marked_wf` |
| Cleanup sim (whole-stack relation) | venom/codegen/proofs/cleanOpsSimScript.sml | `clean_ops_sim` (venom_asm_rel, stack <= 17), `popmany_individual_sim`, `popmany_plan_top_two_sim`, mark-dead lemmas (`[local]`) |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `clean_stack_plan_def` (l.719), `mark_dead_stack_def`, `below_all_live_def`, `dead_stack_marker_def`, `generate_phi_plan_def` (l.129), `generate_inst_plan_def`, `generate_block_insts_plan_def`, `generate_block_plan_def`, `phi_block_ready_def`, `phi_uses_disjoint_def`, `block_entries_ready_def`, `phi_operands_ready_def`, `codegen_ready_fn_def`, `non_param_insts_def`, `get_params_def` |
| Stack model / ops | venom/codegen/defs/stackModelScript.sml, venom/codegen/defs/stackPlanOpsScript.sml, venom/codegen/defs/stackPlanTypesScript.sml | `stack_get_phi_depth_def`, `stack_peek`, `stack_poke`, `do_swap`, `do_dup`, `popmany_plan`, `popmany_individual` |
| Lineage states | venom/codegen/proofs/fnPlanLineageScript.sml, venom/codegen/proofs/fnLineageStaticScript.sml | `lineage_entry_def` (l.149), `lineage_state`, `dfs_block_state`; `lineage_state_static` |
| Frame invariant | venom/codegen/defs/frameRelScript.sml | `fn_frame_inv_def`, `frame_view_def`, `frame_view_vars_lookup`, `frame_view_non_retpc` |
| Relations | venom/codegen/defs/contextCodegenRelScript.sml, venom/codegen/defs/codegenRelScript.sml | `context_venom_asm_rel_def`, `venom_asm_rel_def`, `plan_stack_rel_def`, `plan_spill_rel` |
| Frame lifting | venom/codegen/proofs/genFrameSimScript.sml | `gen_jmp_frame_sim` (l.260) and `gen_inst_frame_sim` (l.1206): how a local `venom_asm_rel` run on the frame's own stack is lifted to `fn_frame_inv` (rest, memory mask, closure spill bytes, region) |
| Frame asm steps | venom/codegen/proofs/asmFrameScript.sml, venom/codegen/proofs/asmFrameHelpersScript.sml, venom/codegen/proofs/stackOpSimScript.sml | `asm_steps_frame`, `asm_pop_frame`, `asm_steps_add_ok` |
| Pop / swap / spill sims | venom/codegen/proofs/regularPostfixSimScript.sml, planAlignScript.sml, doSwapSimScript.sml, spillSimScript.sml, reorderSpillFreshScript.sml, planSpillBoundsScript.sml, allocMonoScript.sml | `popmany_plan_top_singleton_sim`, `popmany_plan_contiguous_sim`, do_swap simulation with spills, `do_swap_spills_fresh_frame`, allocator monotonicity |
| Single-instruction sim | venom/codegen/proofs/genBlockSimScript.sml | `gen_inst_ok_sim` (exported; has a PHI case), `generated_plan_state_wf_def`; PHI helpers around l.4499-4700 (`[local]`: read for ideas) |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | `resolve_phi_def` (l.198), `eval_one_phi`, `eval_phis_def` (l.1662), `phi_prefix_length_def` (l.1676) |
| Liveness / DFG | venom/analysis/liveness/defs/livenessDefsScript.sml, venom/analysis/liveness/proofs/, venom/analysis/dfg/defs/dfgDefsScript.sml | `input_vars_from_def`, `collect_phis_def`, `live_vars_at`, `normalize_operand_def` |
| Unit shape | venom/compiler/unitShapeDefsScript.sml | `retpc_shape_ok_def`, `opaque_use_ok_def`, `retpc_var` |
| Project guide | AGENTS.md, docs/HOL4_PROOF_CONTROL_LESSONS.md | repo proof conventions |
| Deep, marker-tolerant frame lemmas | venom/codegen/proofs/fnFrameDeepHaltScript.sml (proved), fnFrameDeepScript.sml and its leaves, fnFrameBoundaryEntryParamsScript.sml (`entry_context_popmany_sim`, needs ALL_DISTINCT stack) | how any-depth stacks with marker slots and spills are handled against fn_frame_inv |

## Notes

- A statement check of the consumer found no counterexample. Facts it relied on: `plan_stack_rel`/`plan_spill_rel` accept `dead_stack_marker` slots (codegenRelScript.sml l.54, 67); cleanup never pops `input_vars_from` variables; spill offsets come from the layout-wf allocator, so they're fresh, distinct and inside `[sa_spill_base, sa_next_offset)`.
- Known gap: existing deep-stack (> 16) swap/pop simulations assume `ALL_DISTINCT ps.ps_stack` (e.g. `entry_context_popmany_sim`, fnFrameBoundaryEntryParamsScript.sml) or a duplicate-free spill chunk (`duplicate_key_spill_restore_not_wf`, doSwapSimScript.sml), while here the stack can repeat `dead_stack_marker`. Another worker is building marker-tolerant deep reorder/emit lemmas on git ref `origin/bot/opus/seq-1260-deep` (`deepResidualSimScript.sml`, `deepResidualBudgetScript.sml`, still admitted); read them for ideas if your git tool allows `git show <ref>:<path>`, don't merge that branch.
- A statement check of this theorem found no counterexample. Facts it relied on: the deep `do_swap` path only changes `ps_stack` and `ps_alloc` (its spill is transient: allocate, spill, restore, free), so cleanup leaves `ps_spilled` unchanged; `do_swap_layout_wf` (doSwapSimScript.sml l.3474); `do_swap_venom_asm_rel_numeric` (doSwapSimScript.sml l.5108) covers any depth without `prefix_spill_wf`, unlike `do_swap_venom_asm_rel_general`, whose `prefix_spill_wf` premise fails on chunks with repeated markers; emitted offsets lie in `[ps2.sa_spill_base, ps2.sa_next_offset)`, inside the region, so `closure_spill_byte_own` and the genFrameSim lifting pattern (l.110-139) apply; asmSem has no stack-height limit.

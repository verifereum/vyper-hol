# TASK: Prove dead-store elimination correct

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/dead_store_elim/proofs

## Theorem Statement (FROZEN)

Both theorems are in
`venom/passes/dead_store_elim/proofs/deadStoreElimProofsScript.sml`,
proved by `cheat`. Replace both cheats with proofs.

```sml
Theorem dse_function_space_correct:
  !analysis_fn space fuel ctx fn s safe_inv.
    wf_function fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ safe_inv s /\
    (!s0 idx. safe_inv (s0 with vs_inst_idx := idx) <=> safe_inv s0) /\
    (!fuel' ctx' inst s0 s1.
       MEM inst (fn_insts fn) /\ safe_inv s0 /\
       step_inst fuel' ctx' inst s0 = OK s1 ==> safe_inv s1) /\
    (!bb s0 s1.
       MEM bb fn.fn_blocks /\ safe_inv s0 /\
       eval_phis s0 bb.bb_instructions = OK s1 ==> safe_inv s1) /\
    (!s0. safe_inv s0 ==>
       alloca_inv s0 /\
       (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                      base + sz < dimword (:256)) /\
       alloca_safe_access fn (alloca_roots fn) s0 /\
       ptrs_in_alloca_bounds fn (alloca_roots fn) s0 /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s0 /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s0 /\
       bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) fn s0) /\
    (!fn'. all_dead_stores (analysis_fn space fn')
             (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
             space fn') ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s)

Theorem dse_function_correct:
  !analysis_fn fuel ctx fn s safe_inv.
    wf_function fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ safe_inv s /\
    (!s0 idx. safe_inv (s0 with vs_inst_idx := idx) <=> safe_inv s0) /\
    (!fuel' ctx' inst s0 s1.
       MEM inst (fn_insts fn) /\ safe_inv s0 /\
       step_inst fuel' ctx' inst s0 = OK s1 ==> safe_inv s1) /\
    (!bb s0 s1.
       MEM bb fn.fn_blocks /\ safe_inv s0 /\
       eval_phis s0 bb.bb_instructions = OK s1 ==> safe_inv s1) /\
    (!s0. safe_inv s0 ==>
       alloca_inv s0 /\
       (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                      base + sz < dimword (:256)) /\
       alloca_safe_access fn (alloca_roots fn) s0 /\
       ptrs_in_alloca_bounds fn (alloca_roots fn) s0 /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s0 /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s0 /\
       bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) fn s0) /\
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
        space fn') ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function analysis_fn fn) s)
```

The pass and its relations are defined in
`venom/passes/dead_store_elim/defs/deadStoreElimDefsScript.sml`
(`all_dead_stores`, `bp_access_ops`, `bp_accesses_in_own_alloca`, `dse_inst`,
`dse_iterate`, `dse_function_space`, `dse_function`, `dse_equiv`,
`dse_all_equiv`).

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * and build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions, decision procedures) that help this proof
 * IS explicitly in scope — even if they take significant
 * effort. They amortize across the project.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build deadStoreElimCorrectnessTheory` passes with zero
   CHEAT warnings and zero failures, at the project's default tactic
   timeout.
2. No cheat is left anywhere under `venom/passes/dead_store_elim/`.
3. The two frozen statements, and the wrappers in
   `venom/passes/dead_store_elim/deadStoreElimCorrectnessScript.sml`,
   are unchanged.
4. No definition outside new helper theories changes, and no new axiom.
5. No duplicate or near-duplicate lemmas: each helper exists once in its
   most general form. Reuse the existing lemmas listed below before
   writing new ones.

**If a theorem is false as stated:**
- Produce a HOL4 counterexample (e.g. `EVAL_TAC` on concrete values),
  next to the existing `dse_function_space_correct_FALSE1..5` theorems.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build deadStoreElimCorrectnessTheory
```

Run from the project root (the directory holding `holproject.toml` and
this file).

## Background

Dead-store elimination (DSE) is one of the Venom IR optimisation passes
of the Vyper compiler, run at O2/O3 once per address space (MEMORY,
STORAGE, TRANSIENT). It turns into NOPs the stores that an analysis
(`analysis_fn`) reports dead, and repeats until no store changes
(`dse_iterate`). `all_dead_stores` is the soundness contract the
analysis must meet; the theorems take it as a premise for every
function, so it also holds for the intermediate functions of the
iteration. The conclusion: either the original run errors, or both runs
end the same way, with states related by `dse_equiv space` (equal apart
from the space DSE touched, where only live locations agree) or
`dse_all_equiv` for the full pass.

`safe_inv` is a caller-supplied invariant of the original function's
reachable states (it holds at the start, survives every step and PHI
evaluation of `fn`), which implies alloca safety and agreement with the
base-pointer analysis, and that every access through an alloca pointer
stays inside that alloca (`may_overlap` treats different allocas as
disjoint). The `FALSE1..5` theorems in the same file show
why each premise is there.

These two theorems are oracle debt in the end-to-end compiler
correctness proof; `lowering/createOracleClosureAuditScript.sml` lists
them.

## Domain Constraints

- holbuild only. Never raise the tactic timeout (2.5 s per proof step in
  this project); a step that runs over is split or given a smaller
  rewrite set.
- No `TRY` or `ORELSE` around `metis_tac` or any other search; select
  goals with `>~`, `>-`, `>|`.
- No `let` in theorem statements.
- Write theories with `Theorem … Proof … QED` under
  `Theory`/`Ancestors`/`Libs` headers.
- Read `AGENTS.md` at the project root: it has the project's layout,
  naming and proof rules, and wins over this file.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Project rules | `AGENTS.md` | Conventions for proofs in this repo |
| DSE defs | `venom/passes/dead_store_elim/defs/deadStoreElimDefsScript.sml` | The pass, `all_dead_stores`, `dse_equiv` |
| DSE frame | `venom/passes/dead_store_elim/defs/deadStoreElimFrameScript.sml`, `venom/passes/dead_store_elim/proofs/deadStoreElimFrameLib.sml` | Frame lemmas and tactics for DSE |
| DSE proofs | `venom/passes/dead_store_elim/proofs/deadStoreElimProofsScript.sml` | The frozen theorems, block-level simulation already proved above them, FALSE1..5 counterexamples |
| DSE wrappers | `venom/passes/dead_store_elim/deadStoreElimCorrectnessScript.sml` | Public wrappers of the two theorems |
| Exec semantics | `venom/defs/venomExecSemanticsScript.sml` | `run_blocks`, `step_inst`, `eval_phis`, `exec_block`, `write_memory_with_expansion` |
| Well-formedness | `venom/defs/venomWfScript.sml` | `wf_function`, `ssa_form` |
| Alloca invariants | `venom/defs/venomMemDefsScript.sml`, `venom/passes/shared/defs/allocaRemapDefsScript.sml` | `alloca_inv`, `alloca_safe_access`, `ptrs_in_alloca_bounds`, `alloca_roots` |
| Result relations | `venom/defs/stateEquivScript.sml`, `venom/props/` | `lift_result`, state-equivalence props |
| Base-pointer analysis | `venom/analysis/base_ptr/defs/basePtrDefsScript.sml`, `venom/analysis/base_ptr/basePtrPropsScript.sml`, `venom/analysis/base_ptr/proofs/basePtrProofsScript.sml` | `bp_analyze`, `bp_ptr_sound`, `bp_ptrs_bounded`, write/read locations |
| Memory locations | `venom/analysis/shared/defs/memLocDefsScript.sml`, `venom/analysis/shared/memLocPropsScript.sml` | `ml_is_fixed`, `ml_size`, location lemmas |
| Memory alias | `venom/analysis/mem_alias/memAliasPropsScript.sml` | `ma_may_alias_sound` and friends |
| Memory SSA | `venom/analysis/mem_ssa/defs/memSSADefsScript.sml`, `venom/analysis/mem_ssa/proofs/memSSAProofsScript.sml` | The analysis DSE consults |
| Pass simulation | `venom/simulation/passSimulationPropsScript.sml`, `venom/simulation/proofs/passSimulationProofsScript.sml`, `venom/simulation/proofs/analysisSimProofsSoundScript.sml` | Generic block/function simulation lemmas |
| Shared pass lemmas | `venom/passes/shared/passSharedPropsScript.sml`, `venom/passes/shared/proofs/` | Frame, field, transfer lemmas reused by many passes |
| Memory props | `venom/props/venomMemPropsScript.sml` | Memory read/write/expansion lemmas |
| Closest proved pass | `venom/passes/memory_copy_elision/memoryCopyElisionCorrectnessScript.sml`, `venom/passes/memory_copy_elision/proofs/memoryCopyElisionSoundScript.sml` | Memory pass proved under the same kind of reachable-state invariant and base-pointer analysis |
| Another reachable-invariant proof | `venom/passes/mem2var/mem2varCorrectnessScript.sml` | Same invariant style |
| Upstream pass | Vyper at `VYPER_PIN`: `vyper/venom/passes/dead_store_elimination.py` (not in this tree) | Reference only |

## Notes

- The previous statements of these theorems were false; `FALSE1..5`
  in the proofs file are the counterexamples, and each premise of the
  current statements excludes one of them.
- Two definitions changed with this statement, to match upstream:
  `bp_segment_from_ops` sizes a location by `iao_size`, not
  `iao_max_size`, and `all_dead_stores` excludes zero-size writes (they
  still expand memory, which `MSIZE` observes).

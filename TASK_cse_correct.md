# TASK: Prove cse_function_correct_proof

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/cse/proofs/cseProofsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem cse_function_correct_proof:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> ALLOCA) /\
    s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_function fn) s)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. Replace the `cheat` in `cse_function_correct_proof` with a proof of the exact frozen formula.
2. `holbuild -j4 build cseProofsTheory cseCorrectnessTheory` passes at the default step limit with zero CHEAT warnings in both theories' build logs.
3. Add no axioms, no new definitions used in the statement, and no new premises. Supporting lemmas are allowed, in the cse proofs directory or, when reusable, in an appropriate existing shared or analysis theory. Reuse existing theorems; no duplicate lemmas.
4. Commit source files only, with the trailer `Bot: opus (Claude Opus 5.5)`. Never commit task files, alan state, logs or probes.

**If the theorem is false as stated:** produce a concrete counterexample (a function, a start state, and the two differing results, checked by evaluation in a scratch theory where feasible), state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```sh
holbuild -j4 build cseProofsTheory cseCorrectnessTheory
```

Keep cache, checkpoints and proof steps on. Never change the tactic timeout. Build changed helper theories by their logical names.

## Background

CSE (common subexpression elimination) is one of the Venom IR optimisation passes in the Vyper compiler model. `cse_function` iterates `cse_single_pass` to a fixpoint (OWHILE), then removes NOPs. Each pass builds the DFG, runs the available-expression dataflow analysis, computes a canonical-producer map (`compute_canon`, modelling Python's object identity through ASSIGN chains), and replaces an instruction whose expression is available with `ASSIGN` from the earlier result, or with `NOP` when it has no outputs.

The theorem says the transformed function simulates the original from the function's entry block: unless the original errors, both runs give equivalent results. The SSA, well-formedness and entry premises are needed: without them the statement is false (starting in a non-entry block where the earlier result is unbound, or a non-SSA redefinition of an operand). The no-ALLOCA premise is needed too: two identical `alloca 32` would be merged, but allocations are keyed by `inst_id`. In the O2/O3 pipeline CSE runs after memory-location concretization, whose output contract has no ALLOCA.

`cse_preserves_ssa_form` and `cse_preserves_wf_function` in `venom/passes/cse/cseCorrectnessScript.sml` are already proved, together with local lemmas on the shape of `cse_inst` and an OWHILE invariant for `cse_iterate`; promote and reuse them as needed.

## Domain Constraints

- Scope: the cse pass directory (`venom/passes/cse/`) and, for genuinely reusable lemmas, existing analysis or shared theories. Do not change any executable definition (`cseDefs`, `availExprDefs`, `dfAnalyzeDefs`, the semantics) or `holproject.toml`.
- `cse_sound_def` in cseProofs is a draft invariant; you may change or drop it, since nothing outside cseProofs uses it.
- No search tactic under `TRY`/`ORELSE`, no tactic-timeout change, no `holbuild run`/`repl`, no Holmake, no interactive sessions.
- Keep proofs within the default 2.5 s per step: split steps, cut rewrite sets. Read `docs/HOL4_PROOF_CONTROL_LESSONS.md`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `venom/passes/cse/proofs/cseProofsScript.sml` | frozen theorem, `cse_sound_def`, proof sketch comment |
| Obligations | `venom/passes/cse/cseCorrectnessScript.sml` | wrapper theorem, proved ssa/wf preservation and cse_inst shape lemmas |
| Pass definition | `venom/passes/cse/defs/cseDefsScript.sml` | `cse_function`, `cse_iterate`, `cse_single_pass`, `compute_canon`, `operand_producer`, `operand_ids_match`, `cse_lookup`, `cse_lookup_same_bb`, `cse_inst`, `expr_depth` |
| Available expressions | `venom/analysis/available_expression/` | `availExprDefsScript.sml` (mk_expr, avail_transfer_inst, avail_remove_effect, avail_meet_two, avail_analyze), `availExprAnalysisPropsScript.sml`, `proofs/availExprProofsScript.sml` |
| Dataflow framework | `venom/analysis/dataflow/` | `df_analyze`, `df_at`, fixpoint/soundness props |
| DFG | `venom/analysis/dfg/` | `dfg_build_function` and its props |
| Analysis-driven simulation | `venom/simulation/` (`analysisSimProps`, `passSimulationProps`, and their proofs) | generic block/function simulation for analysis-based instruction rewrites, MAPi/function_map_transform toolkit |
| Shared pass lemmas | `venom/passes/shared/passSharedPropsScript.sml` | `clear_nops_function` lemmas, `mk_assign_inst`, `mk_nop_inst` |
| NOP removal equivalence | `venom/passes/dead_store_elim/proofs/deadStoreElimProofsScript.sml` (`clear_nops_function_dse_equiv`) | how another pass proved run equivalence across clear_nops |
| Comparable proofs | `venom/passes/assign_elim/proofs/`, `venom/passes/memory_copy_elision/proofs/` | analysis-driven rewrite passes proved under the same premises (wf_function, wf_ssa, entry label) |
| Semantics | `venom/semantics/`, `venom/defs/` | `run_blocks`, `step_inst`, `lift_result`, `state_equiv`, `execution_equiv`; `wf_function`, `wf_ssa`, `def_dominates_uses` in `venom/defs/venomWfScript.sml` |
| Effects | grep `Theory venomEffects` | read/write effects per opcode, `is_nonidempotent` |
| Proof conventions | `AGENTS.md`, `docs/HOL4_PROOF_CONTROL_LESSONS.md` | project rules |

## Notes

The statement builds with `cheat`. Its premises were checked by an independent statement review before launch; that review found the ALLOCA case, now excluded by a premise.

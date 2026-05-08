# Proof Roadmap: Compiler Correctness

## Overview

The compiler correctness theorem (`vyper_call_correct`) is proved but depends
on 7 bridge cheats and ~56 pass-level cheats. This roadmap shows the
dependency ordering for closing them.

## Three-Level Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    TOP LEVEL: vyper_call_correct                  │
│  (compile_vyper → EVM execution matches call_external)           │
└────────┬───────────────────┬────────────────────┬────────────────┘
         │                   │                    │
    LEG 1: Lowering    LEG 2: Pipeline       LEG 3: Codegen
    (Vyper → Venom)    (Venom → Venom)      (Venom → EVM)
    1 bridge cheat      0 bridge cheats      3 bridge cheats
    + lowering proofs   + 56 pass cheats     + 1 EVM bridge cheat
```

## Bridge Cheats (7 total)

| # | Cheat | Location | Dependencies | Priority |
|---|-------|----------|-------------|----------|
| B1 | `vyper_lowering_logs_correct` | e2eCorrectnessScript | Lowering proofs (6 worktrees) | P1 |
| B2 | `codegen_implies_wf` | e2eCorrectnessScript | Codegen def analysis | P2 |
| B3 | `codegen_implies_mem_safe` | e2eCorrectnessScript | Codegen spill analysis | P2 |
| B4 | `codegen_implies_entry_fn_no_ret` | e2eCorrectnessScript | Codegen def analysis | P2 |
| B5 | `evm_correspondence_to_call_result` | e2eCorrectnessScript | VFM run_call semantics | P2 |
| B6 | `evm_revert_state_unchanged` | e2eCorrectnessScript | EVM handle_exception trace | P2 |
| B7 | `o2_pipeline_ctx_pass_correct` | e2eCorrectnessScript | All O2 pass proofs | P3 |

## Pass-Level Cheats by Category

### Category 1: Simple pass_correct migration (lift_result → pass_correct)
These passes have proved `lift_result` statements. Need:
- `run_blocks_deterministic` for both sides
- Apply `lift_result_implies_pass_correct`

| Pass | Current | Cheats | Work | Blocked by |
|------|----------|--------|------|-----------|
| assert_combiner | `lift_result (state_equiv fresh)` | 1 | migration | — |
| branch_opt | `lift_result (state_equiv fresh)` | 1 | migration | — |
| single_use_expansion | `lift_result (state_equiv fresh)` | 2 | migration | — |
| affine_folding | `lift_result (state_equiv {})` | 1 | migration | — |

### Category 2: Error disjunction elimination before migration
These passes have `lift_result` with an Error disjunct. Need stronger
preconditions (wf_ssa/dominance) to guarantee no Error.

| Pass | Current | Cheats | Work | Blocked by |
|------|----------|--------|------|-----------|
| overflow_elim | `lift_result` + Error disj | 0 (proof done) | eliminate error + migrate | — |
| assign_elim | `lift_result` + Error disj | 0 (proof done) | eliminate error + migrate | wf_ssa/dominance def |

### Category 3: Partial block-level simulation proofs
These have block-level simulation but need function-level `pass_correct`.

| Pass | Current | Cheats | Blocked by |
|------|----------|--------|-----------|
| remove_unused | per-block sim | 5 | alloca-sunset def changes |
| dft | per-block sim | 5 | alloca-sunset (sort key rewrite) |
| memmerging | per-block sim | 4 | standalone |
| concretize_mem_loc | fragmented | 13 | alloca-sunset |
| dead_store_elim | per-block sim | 2 | alloca-sunset (volatiles) |
| load_elim | per-block sim | 2 | standalone |
| mem2var | per-block sim | 2 | alloca-sunset |
| memory_copy_elision | fragmented | 1 | standalone |
| tail_merge | per-block sim | 2 | standalone |
| simplify_cfg | `result_equiv` | 3 | standalone |
| cfg_normalization | `result_equiv` | 2 | fresh label precondition |
| single_use_expansion | see Cat 1 | 2 | standalone |
| sccp | `pass_correct` | 1 | SAR edge case |

### Category 4: Complex passes with custom relations
| Pass | Current | Cheats | Notes |
|------|----------|--------|-------|
| cse | `pass_correct` (cheated) | 3 | OWHILE induction |
| algebraic_opt | `pass_correct` (cheated) | 1 | per-opcode cases |
| function_inliner | separate proof | varies | interprocedural |

## Dependency Ordering

### Phase 1: Unlock blocked passes (alloca-sunset)

The `alloca-sunset` merge (removing PALLOCA/CALLOCA) affects 7 passes (31 cheats).
These can't be proved until the definitions stabilize.

**Action**: Complete alloca-sunset merge, then rebase+prove blocked passes.

### Phase 2: Simple migrations (4-6 passes)

After Phase 1, migrate the simplest passes from `lift_result` to `pass_correct`:
- assert_combiner, branch_opt, single_use_expansion, affine_folding
- overflow_elim (with Error elimination)
- assign_elim (with Error elimination — needs wf_ssa/dominance)

### Phase 3: Complete per-pass proof work (31+ cheats)

Blocks of independent work:
- **Standalone**: memmerging (4), load_elim (2), tail_merge (2), memory_copy_elision (1)
- **After alloca-sunset**: remove_unused (5), dft (5), concretize_mem_loc (13), dead_store_elim (2), mem2var (2), sccp (1)
- **Complex**: cse (3), algebraic_opt (1), simplify_cfg (3), cfg_normalization (2)

### Phase 4: Bridge proofs (7 cheats)

After all pass proofs complete:
1. B2-B4: codegen structural (codegen_implies_wf/mem_safe/entry_fn_no_ret)
2. B5-B6: EVM semantics (evm_correspondence_to_call_result, evm_revert_state_unchanged)
3. B1: lowering correctness (vyper_lowering_correct) — largest piece, depends on lowering worktrees
4. B7: O2 pipeline instance composition

## Semantic Connection Map

Every pass correctness theorem relates to Vyper-HOL semantics through:

```
pass_correct R_ok R_term R_abort
  where R_ok = state_equiv fresh_vars
        R_term = execution_equiv fresh_vars (or UNIV)
        R_abort = execution_equiv fresh_vars (or revert_equiv)

state_equiv vars s1 s2  ⟺
  (∀x. x ∉ vars ⟹ lookup_var x s1 = lookup_var x s2) ∧
  s1.vs_memory = s2.vs_memory ∧
  s1.vs_storage = s2.vs_storage ∧
  s1.vs_transient_storage = s2.vs_transient_storage ∧
  s1.vs_logs = s2.vs_logs ∧
  ...

observable_equiv s1 s2  ⟺  state_equiv {} s1 s2
  (all variables match, all memory/storage/logs match)

R_ok ⇒ observable_equiv when fresh_vars ∩ observable_vars = {}
```

The pipeline composition ensures that the composed R_ok for O2 implies
`observable_equiv`, which is sufficient for the e2e theorem to conclude
EVM results correspond to Vyper source semantics.

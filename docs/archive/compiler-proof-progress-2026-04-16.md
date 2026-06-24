# Vyper-HOL Compiler Correctness: Progress Dashboard

> Historical snapshot. Counts and statuses may be stale; see
> [../compiler-proof-status.md](../compiler-proof-status.md) for the latest audit.

**Generated:** 2026-04-16  
**Codebase:** 444 theory files, ~300K LOC, 207 total cheats  
**Since 2026-04-07:** ~28 cheats removed; arithmeticProps, contextProps, assign_elim, make_ssa, assert_elim, affine_folding, overflow_elim, allocaRemapProofs all proved out

## Architecture

```
  Vyper Source (call_external)
          │
          │  [Leg 1] vyper_to_venom_correct
          ▼
  Venom IR (run_context on lowered ctx)
          │
          │  [Leg 2] venom_pipeline_correct ✅
          ▼
  Venom IR (run_context on optimized ctx)
          │
          │  [Leg 3] codegen_correct
          ▼
  EVM Bytecode (vfm step)
```

## Overall Status

| Area | Files | LOC | Cheats | Status |
|------|------:|----:|-------:|:-------|
| Syntax + Frontend | 5 | ~2K | 0 | ✅ Complete |
| Vyper Semantics (defs) | 10 | ~5K | 0 | ✅ Complete |
| Vyper Semantics (properties) | 25 | ~33K | 0 | ✅ Complete |
| Venom Core (defs+proofs+props) | 14 | ~11K | 1 | ✅ Near-complete |
| Venom Simulation Framework | 22 | ~15K | 0 | ✅ Complete |
| Venom Analysis | 55 | ~47K | 0 | ✅ Complete |
| Venom Passes (32 passes) | 120 | ~143K | 125 | 🟡 Major progress |
| Venom Codegen | 45 | ~23K | 18 | 🟡 Substantial proof infrastructure done |
| Lowering (Vyper→Venom) | 39 | ~23K | 63 | 🔴 Core gap |
| E2E Composition | — | — | (in lowering) | 🔴 Depends on legs 1+3 |
| **Total (non-test)** | **444** | **~300K** | **207** | |

392 of 444 theory files are cheat-free (88%).

---

## Leg 1: Lowering — 🔴 PRIMARY BOTTLENECK (63 cheats)

**The largest gap.** Definitions are complete and cheat-free. Correctness theorems are mostly cheated.

### Progress since Apr 7
- **arithmeticProps** (13 cheats → 0) ✅ Fully proved (2665 LOC proof)
- **contextProps** (12 cheats → 0) ✅ Fully proved (638 LOC proof)

### Remaining cheats by file

| File | Cheats | Description |
|------|-------:|:------------|
| `stmtLoweringPropsScript` | 14 | If, for, assign, return, assert compilation |
| `abiEncoderPropsScript` | 11 | ABI encoding/decoding, element ptr, zero pad |
| `builtinPropsScript` | 11 | keccak256, unsafe arith, min/max, abs, shift, raw_call, create |
| `e2eCorrectnessScript` | 10 | E2E composition layer (bridges all 3 legs) |
| `exprLoweringPropsScript` | 8 | Literal, name, binop, neg, env var compilation |
| `compileEnvScript` | 3 | Compiler environment setup |
| `moduleLoweringPropsScript` | 3 | Selector dispatch, arg decode, entry checks |
| `vyperLoweringCorrectScript` | 1 | Top-level `vyper_to_venom_correct` |
| `contextScript` (defs) | 1 | Context definition helper |
| `builtinTypeConvertPropsScript` | 1 | Type conversion properties |

**Cheated areas broken down by topic:**
- Statement compilation: 14 cheats (if/for/assign/return/assert)
- Expression compilation: 8 cheats (literals/names/binops/env vars)
- Builtins: 12 cheats (hashing, arith, create, type convert)
- ABI: 11 cheats (encode/decode)
- E2E composition: 10 cheats
- Memory/storage/context: 4 cheats
- Module lowering: 3 cheats

---

## Leg 2: Venom Pipeline — 🟡 125 cheats across 32 passes

Pipeline composition framework is **fully proven** (0 cheats). Simulation framework is **fully proven** (0 cheats). Individual pass status:

### ✅ Fully Proven (0 cheats) — 7 passes

| Pass | Notes |
|------|:------|
| **SCCP** | Complex dataflow, fully verified |
| **assign_elim** | Was 2 cheats → 0 |
| **make_ssa** | Was 3 cheats → 0 |
| **assert_elim** | Was 2 cheats → 0 |
| **affine_folding** | Was 1 cheat → 0 |
| **overflow_elim** | Was 1 cheat → 0 |
| **invoke_copy_fwd_common** | Shared infrastructure |

### 🟢 Core Done, Only SSA/WF Obligations (2 cheats each) — 7 passes

These have semantic correctness fully proven; only `preserves_ssa_form` / `preserves_wf_function` remain cheated.

| Pass |
|------|
| **assert_combiner** |
| **branch_opt** |
| **lower_dload** |
| **phi_elimination** |
| **revert_to_assert** |
| **single_use_expansion** |
| **mem2var** |

### 🟡 Partially Proven (1–6 cheats) — 10 passes

| Pass | Cheats | Notes |
|------|-------:|:------|
| **simplify_cfg** | 6 | CFG simplification + structural obligations |
| **cfg_normalization** | 5 | CFG normalization + obligations |
| **dft** | 7 | Deepest remaining pass proof; alloca invariant preservation |
| **cse** | 4 | Common subexpression elimination |
| **dead_store_elim** | 4 | Dead store elimination |
| **load_elim** | 4 | Load elimination |
| **tail_merge** | 4 | Tail merging |
| **function_inliner** | 4 | Function inlining |
| **fix_mem_locations** | 3 | Memory location fixing |
| **algebraic_opt** | 3 | Algebraic optimization |
| **literals_codesize** | 2 | Literals/codesize handling |
| **memmerging** | 1 | Memory merging (mostly done) |
| **internal_return_copy_fwd** | 1 | Internal return copy forwarding |
| **readonly_invoke_copy_fwd** | 1 | Readonly invoke copy forwarding |

### 🔴 Largely Cheated (7+ cheats) — 2 passes

| Pass | Cheats | Notes |
|------|-------:|:------|
| **concretize_mem_loc** | 13 | Alloca invariant preservation (4 step_inst + 4 exec_block + 5 misc) |
| **memory_copy_elision** | 42 | Active work-in-progress (191K LOC proof file, 41 cheats in proofs + 1 in correctness) |

### Shared Infrastructure (5 cheats)

| File | Cheats | Status |
|------|-------:|:-------|
| `copyFwdEquivScript` | 4 | Was 7 → 4 (3 removed) |
| `passSharedPropsScript` | 1 | |
| `allocaRemapProofsScript` | 0 | ✅ Was 7 → 0! |

---

## Leg 3: Codegen — 🟡 18 cheats (was 13, but proof infrastructure grew massively)

The codegen proofs/ directory expanded from ~nothing to **19K LOC** across 28 proof files, with only **11 cheats in genBlockSimScript**. Most per-instruction simulation proofs are done.

| Component | Cheats | Status |
|-----------|-------:|:-------|
| Per-instruction sim (28 proof files) | 11 | 🟡 One file (genBlockSim) has 11 cheats; 27 files are cheat-free |
| `codegenCorrectnessScript` | 3 | 🔴 Top-level: gas model + final assembly |
| `venomToAsmPropsScript` | 3 | 🔴 Venom→ASM translation |
| `asmToBytecodePropsScript` | 1 | 🔴 ASM→bytecode |

**genBlockSimScript cheats breakdown** (11 total):
- Per-instruction Halt/Abort simulation cases
- clean_stack_plan simulation
- Block-level composition gaps

---

## E2E Composition — 🔴 10 cheats (in `lowering/e2eCorrectnessScript`)

The E2E file lives in lowering/ and has 10 cheats. These are composition-level gaps that depend on Leg 1 and Leg 3 being resolved.

| Theorem | Status |
|---------|:------:|
| `vyper_call_correct` | 🔴 (depends on lowering + codegen) |
| `e2e_vyper_to_evm` | 🔴 (all three legs) |
| `venom_pipeline_correct` | ✅ |
| `compile_vyper_runtime_bytecode` | ✅ |

---

## What's Missing for the Final Result

### Must-close (blocking end-to-end theorem)

1. **Lowering correctness (~53 cheats, excluding e2e)** — The dominant gap. Requires bridging Vyper big-step evaluation to Venom instruction sequences across statements, expressions, builtins, and ABI encoding.

2. **Codegen top-level correctness (~7 cheats)** — `codegenCorrectnessScript` (3), `venomToAsmPropsScript` (3), `asmToBytecodePropsScript` (1). The per-instruction simulation is largely done; the gap is composing these into block-level and function-level theorems.

3. **E2E composition (10 cheats)** — Glue layer that composes the three legs. Depends on #1 and #2.

### Should-close (pass correctness, not blocking e2e but required for full pipeline)

4. **SSA/WF preservation obligations (~14 cheats across 7 passes)** — Repetitive structural proofs. Could potentially be batch-proven.

5. **Individual pass block simulations (~40 cheats across 12 passes)** — Each needs a pass-specific block-level simulation lemma, but they follow the simulation framework pattern.

6. **memory_copy_elision (42 cheats)** — Active WIP in a 191K LOC proof file. Largest single-pass cheat count.

7. **concretize_mem_loc (13 cheats)** — Alloca invariant preservation for concrete memory locations.

8. **dft pass (7 cheats)** — Alloca invariant preservation + instruction commutation.

9. **copyFwdEquiv shared proofs (4 cheats)** — Blocks ircf/ricf/mce full completion.

### Nice-to-close (not blocking any other proof)

10. **Venom core exec_equiv (1 cheat)** — `run_function` entry-label case.

---

## Cheat Summary

| Area | Cheats | % of Total |
|------|-------:|-----------:|
| Lowering (Leg 1) | 63 | 30% |
| Pass proofs (semantic) | ~65 | 31% |
| Pass obligations (ssa/wf) | ~14 | 7% |
| Pass WIP (mce + cml) | 55 | 27% |
| Codegen (Leg 3) | 18 | 9% |
| Venom core | 1 | <1% |
| **Total** | **207** | |

### Cheats Removed Since Apr 7

| Area | Before | After | Δ |
|------|-------:|------:|--:|
| arithmeticProps | 13 | 0 | -13 |
| contextProps | 12 | 0 | -12 |
| assign_elim | 2 | 0 | -2 |
| make_ssa | 3 | 0 | -3 |
| assert_elim | 2 | 0 | -2 |
| affine_folding | 1 | 0 | -1 |
| overflow_elim | 1 | 0 | -1 |
| allocaRemapProofs | 7 | 0 | -7 |
| copyFwdEquiv | 7 | 4 | -3 |
| semantics typecheck | 1 | 0 | -1 |
| **Removed** | | | **-45** |
| *Added (expanded proofs)* | | | +17 |
| **Net change** | ~235 | 207 | **-28** |

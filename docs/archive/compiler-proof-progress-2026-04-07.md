# Vyper-HOL Compiler Correctness: Progress Dashboard

> Historical snapshot. Counts and statuses may be stale; see
> [../compiler-proof-status.md](../compiler-proof-status.md) for the latest audit.

**Generated:** 2026-04-07  
**Codebase:** 369 theory files, ~162K LOC, 3832 theorems, 2211 definitions

## End-to-End Architecture

The top-level correctness theorem (`vyper_call_correct` / `e2e_vyper_to_evm`)
decomposes into three legs:

```
  Vyper Source Semantics (call_external)
          │
          │  [Leg 1] vyper_to_venom_correct
          │  Vyper big-step ≈ Venom run_context
          ▼
  Venom IR Execution (run_context on lowered ctx)
          │
          │  [Leg 2] venom_pipeline_correct
          │  run_context(ctx) ≈ run_context(pipeline(ctx))
          │  Composed from 25+ individual pass correctness proofs
          ▼
  Venom IR Execution (run_context on optimized ctx)
          │
          │  [Leg 3] codegen_correct → e2e_venom_to_evm
          │  Venom run_context ≈ EVM bytecode execution (run_call)
          ▼
  EVM Bytecode Execution (vfm step)
```

---

## Overall Status Summary

| Component                     | Files | Theorems | Cheats | Status        |
|-------------------------------|------:|---------:|-------:|:--------------|
| Vyper Syntax                  |     2 |        0 |      0 | ✅ Complete   |
| Vyper Semantics (defs)        |    10 |     ~130 |      1 | ✅ Near-complete (1 typecheck cheat) |
| Vyper Semantics (properties)  |    25 |      735 |      0 | ✅ Complete   |
| Venom Core (defs+proofs+props)|    14 |     ~200 |      2 | ✅ Near-complete (2 mem cheats) |
| Venom Simulation Framework    |    22 |      246 |      0 | ✅ Complete   |
| Venom Analysis                |    55 |      960 |      7 | ✅ Near-complete |
| Venom Passes (26 passes)      |   120 |    ~1400 |   ~100 | 🟡 Substantial progress |
| Venom Codegen                 |    17 |       26 |     13 | 🔴 Mostly cheated |
| Lowering (Vyper → Venom)      |    30 |     ~400 |     96 | 🔴 Mostly cheated |
| E2E Composition               |     2 |       18 |      5 | 🔴 Cheated (glue layer) |
| **Total**                     |**297**|**~4100** |**~224**|               |

297 of 369 non-test theory files are cheat-free.

---

## Leg 1: Lowering (Vyper Source → Venom IR) — 🔴 HARDEST GAP

**Status: ~96 cheats across 10 files. Nearly all correctness theorems cheated.**

This is the largest and hardest gap. The lowering definitions (19 files, ~300
definitions) are complete and cheat-free, but essentially every correctness
property is cheated.

### Breakdown by Area

| File                         | Thms | Cheats | Description |
|------------------------------|-----:|-------:|:------------|
| `vyperLoweringCorrectScript` |    1 |      1 | Top-level: `vyper_to_venom_correct` — cheated |
| `stmtLoweringPropsScript`    |   17 |     14 | Statement compilation (if, for, assign, return, assert) |
| `exprLoweringPropsScript`    |   19 |      9 | Expression compilation (literal, name, binop, neg, env vars) |
| `builtinPropsScript`         |   21 |     20 | Builtins (keccak256, unsafe arith, min/max, abs, shift, raw_call, create, abi encode/decode) |
| `arithmeticPropsScript`      |   13 |     13 | Safe arithmetic (add, sub, mul, div, mod, clamp, compare, decimal div) |
| `contextPropsScript`         |   15 |     12 | Memory/storage ops (ptr_load, ptr_store, nonreentrant lock, copy, zero) |
| `abiEncoderPropsScript`      |   11 |     11 | ABI encoding/decoding, element ptr, zero pad |
| `moduleLoweringPropsScript`  |    9 |      7 | Selector dispatch, arg decode, entry checks, constructor epilogue |
| `emitHelperPropsScript`      |   56 |      0 | ✅ Emit helpers (instruction emission) — fully proven |
| `valueEncodingPropsScript`   |   20 |      0 | ✅ Value encoding — fully proven |

**What makes this hard:** Each correctness theorem relates Vyper big-step
evaluation to Venom instruction sequences. This requires bridging two very
different semantic models (environment + scoped variables vs. flat SSA state),
handling ABI encoding, storage layout, memory allocation, and all the
complexity of Vyper's type system and control flow.

---

## Leg 2: Venom Optimization Pipeline — 🟡 MAJOR PROGRESS

**Status: Pipeline composition framework is fully proven. 2-3 passes fully
done. Most passes have core soundness proofs done; remaining cheats are
structural obligations (preserves_ssa, preserves_wf).**

### Pipeline Composition (✅ Complete)

The `venomPipelineCorrectScript` provides:
- `compose_passes_correct` — N-ary pipeline composition via list induction
- `venom_pipeline_correct` — 5-phase pipeline theorem  
- `apply_ctx_fn_transform_correct` — lift per-block simulation to context level
- `pass_correct_implies_observable` — derive observable equivalence
- `foldl_rel_seq_preserves_observable` — compose observable relations

All proofs complete, no cheats.

### Simulation Framework (✅ Complete, 246 theorems)

The `venom/simulation/` framework is fully proven:
- `passSimulationProofs` — module-level simulation (34 thms)
- `execEquivParamProofs` — parameterized execution equivalence (81 thms)
- `crossBlockSimProofs` — cross-block simulation (5 thms)
- `analysisSimProofs` — analysis-guided simulation (57 thms)
- `instIdxIndep` / `jumpIndep` — independence lemmas (69 thms)

### Individual Pass Status

#### ✅ Fully Proven (0 cheats anywhere)

| Pass | Internal Thms | Notes |
|------|-------------:|:------|
| **SCCP** (sparse conditional constant propagation) | 105 | Complex dataflow, fully verified! |
| **invoke_copy_fwd_common** | 0 | Shared infrastructure |

#### 🟢 Core Proof Done (cheats only in preserves_ssa / preserves_wf obligations)

These passes have their **semantic correctness fully proven**; only the
structural obligation theorems (`preserves_ssa_form`, `preserves_wf_function`)
are cheated. These are boilerplate proofs about syntactic well-formedness
preservation.

| Pass | Internal Thms | Correctness Cheats | Obligation Cheats |
|------|-------------:|-------------------:|------------------:|
| **assert_combiner** | 156 | 0 | 2 (ssa, wf) |
| **assign_elim** | 34 | 0 | 2 (ssa, wf) |
| **branch_opt** | 20 | 0 | 2 (ssa, wf) |
| **lower_dload** | 92 | 0 | 2 (ssa, wf) |
| **phi_elimination** | 14 | 0 | 2 (ssa, wf) |
| **revert_to_assert** | 1 | 0 | 2 (ssa, wf) |
| **single_use_expansion** | 46 | 0 | 2 (ssa, wf) |
| **remove_unused** | 204 | 0 | 2 (alloca confinement) |
| **memmerging** (copy equiv) | 23 | 0 | 2 (ssa, wf) |

#### 🟡 Core Proof Partially Done (some semantic cheats remain)

| Pass | Internal Thms | Proofs/ Cheats | Correctness Cheats | Notes |
|------|-------------:|---------------:|-------------------:|:------|
| **dft** (depth-first traversal) | 8 | 8 | 2 + `independent_commute`, `dft_block_simulates`, `dft_preserves_single_use_form` | Hardest pass proof |
| **memmerging** | 23 | 0 in copy_equiv, 7 in mmCorrectness | 4 | Block simulation cheated |
| **simplify_cfg** | 1 | 2 | 3 (+ `establishes_all_reachable`) | |
| **cfg_normalization** | 1 | 2 | 3 (+ `establishes_normalized_cfg`) | |
| **make_ssa** | 1 | 2 | 3 (+ `establishes_ssa_form`) | |
| **function_inliner** | 1 | 2 | 1 (`preserves_wf`) | |
| **literals_codesize** | 3 | 3 | 2 | |

#### 🔴 Core Proofs Largely Cheated (1-2 internal proof theorems, both cheated)

Many of these have the **definition** and **theorem statement** done, but the
proof body is `cheat`. Each typically needs one block-level simulation lemma
to be proven.

| Pass | Proof Thms | Cheated |
|------|----------:|--------:|
| affine_folding | 1 | 1 |
| algebraic_opt | 1 | 1 |
| assert_elim | 2 | 2 |
| concretize_mem_loc | 2 | 2 |
| cse | 1 | 2 |
| dead_store_elim | 2 | 2 |
| fix_mem_locations | 1 | 1 |
| internal_return_copy_fwd | 1 | 1 |
| load_elim | 2 | 2 |
| mem2var | 1 | 1 |
| memory_copy_elision | 1 | 1 |
| overflow_elim | 1 | 1 |
| readonly_invoke_copy_fwd | 1 | 1 |
| tail_merge | 1 | 2 |

### Shared Infrastructure Cheats (14 cheats)

The `venom/passes/shared/proofs/` directory has 14 cheats in two files:
- `allocaRemapProofsScript.sml` — 7 cheats (alloca pointer remapping for
  passes that change memory layout)
- `copyFwdEquivScript.sml` — 7 cheats (copy-forward equivalence proofs
  shared by ircf/ricf/memory_copy_elision)

These are **blocking dependencies** for multiple passes.

### Cross-Cutting "preserves_ssa_form" / "preserves_wf_function" Obligations

**~50 cheats across 25 passes.** Each pass needs to prove it preserves
SSA form and well-formedness. These are **structurally similar** proofs
(show that the transformation doesn't introduce duplicate definitions,
doesn't break block structure, etc.). A systematic approach could close
many of these relatively quickly.

---

## Leg 3: Codegen (Venom IR → EVM Bytecode) — 🔴 MOSTLY CHEATED

**Status: 13 cheats across 4 files. Architecture defined but proofs not started.**

| File | Thms | Cheats | Description |
|------|-----:|-------:|:------------|
| `codegenCorrectnessScript` | 2 | 2 | `codegen_correct`, `codegen_fn_correct` |
| `venomToAsmPropsScript` | 3 | 3 | Venom → assembly IR translation |
| `asmToBytecodePropsScript` | 6 | 6 | Assembly IR → EVM bytecode |
| `stackPlanGenScript` | 4 | 2 | Stack plan generation correctness |
| `asmToBytecodeProofsScript` | 13 | 0 | ✅ Assembly helpers (parse, label) |

The codegen has a well-defined architecture:
1. Venom IR → Assembly IR (instruction selection, stack planning)
2. Assembly IR → EVM bytecode (label resolution, encoding)

The EVM semantics come from `vfmExecution` (verifereum). The relation
between Venom state and EVM state is defined in `codegenRelScript.sml`.

---

## E2E Composition — 🔴 TOP-LEVEL CHEATED

| Theorem | Status | Depends On |
|---------|:------:|:-----------|
| `vyper_call_correct` | 🔴 cheated | All three legs + EVM framing |
| `e2e_vyper_to_evm` | 🔴 cheated | All three legs composed |
| `e2e_vyper_to_evm_O2` | 🔴 cheated | e2e + pipeline instantiation |
| `e2e_venom_to_evm` | 🔴 cheated | Codegen leg |
| `compile_vyper_raw_well_formed` | 🔴 cheated | Lowering + pipeline WF |
| `e2e_venom_pipeline` | ✅ proven | Pipeline framework |
| `compile_vyper_runtime_bytecode` | ✅ proven | Compilation chain |
| `e2e_deploy_correctness` | trivial (T) | Not yet specified |

---

## Fully Proven Infrastructure

These components have **zero cheats** and provide the foundation:

- **Vyper AST** (syntax/): Type definitions
- **Vyper Semantics properties** (semantics/prop/): 735 theorems about the interpreter
- **Venom Simulation Framework** (simulation/): 246 theorems, the backbone for all pass proofs
- **Venom State Equivalence** (defs/ + proofs/): Reflexivity, symmetry, transitivity, preservation
- **Venom Analysis: CFG** (88 thms), **Dataflow** (205 thms), **DFG** (75 thms), **Dominators** (56 thms), **FCG** (64 thms), **Liveness** (125 thms), **Available Expression** (50 thms), **Stack Order** (68 thms), **Variable Range** (82 thms), **Mem SSA** (24 thms)
- **Pipeline Composition** (compiler/): compose_passes_correct, venom_pipeline_correct

---

## Dependency Graph & Critical Path

```
                    vyper_call_correct
                    /        |         \
                   /         |          \
  vyper_to_venom_correct  pipeline   e2e_venom_to_evm
       [96 cheats]        correct    [13 codegen cheats]
            |               |              |
     ┌──────┼───────┐       |        ┌─────┼──────┐
     │      │       │       │        │     │      │
   stmt   expr   builtin   pass    venom  asm    asm→
   lower  lower  lower   compose  →asm   sem    bytes
   [14]   [9]    [20]     [✅]    [3]    [0]    [6]
     │      │       │               │
     │      │       │          stack_plan
   arith  context  abi_enc     gen [2]
   [13]   [12]     [11]
```

## Hardest Gaps (Priority Order)

### 1. 🔴 Lowering Correctness (~96 cheats) — THE BOTTLENECK

This is by far the largest gap. Every theorem relating Vyper evaluation
to Venom execution is cheated. The difficulty lies in:
- Bridging scoped Vyper environments to flat Venom SSA state
- ABI encoding/decoding correctness (11 cheats in abiEncoderProps)
- Safe arithmetic semantics (13 cheats — each overflow check case)
- Builtin function compilation (20 cheats — keccak, raw_call, create, etc.)
- Memory/storage layout correspondence (12 cheats in contextProps)

### 2. 🔴 Codegen Correctness (13 cheats)

The Venom → EVM translation proof. Requires showing:
- Stack plan execution matches Venom instruction semantics
- Assembly-to-bytecode label resolution is correct
- Gas model admits the execution

### 3. 🟡 Shared Pass Infrastructure (14 cheats)

`allocaRemapProofs` (7 cheats) and `copyFwdEquiv` (7 cheats) block
multiple pass proofs. Fixing these would unblock ircf, ricf, memory
copy elision, and remove_unused alloca handling.

### 4. 🟡 SSA/WF Preservation (~50 cheats across 25 passes)

Repetitive structural proofs. Could potentially be automated or
batch-proven with a common proof strategy.

### 5. 🟡 DFT Pass (8 cheats)

The depth-first traversal pass has the most complex remaining
correctness argument among individual passes. Key gap:
`independent_commute` — showing reordering independent instructions
is semantics-preserving.

### 6. 🟡 Individual Pass Block Simulations (~20 cheats)

~15 passes need their block-level simulation lemma proven. These
follow a common pattern (via the simulation framework) but each
has pass-specific reasoning.

---

## Metrics

| Metric | Value |
|--------|------:|
| Total theory files | 369 |
| Cheat-free files | 297 (80%) |
| Total theorems | 3,832 |
| Total definitions | 2,211 |
| Total cheats | ~235 |
| Total LOC | ~162K |
| Proven Proof blocks | ~4,700 of ~5,000 |

### Cheats by Area
| Area | Cheats | % of Total |
|------|-------:|-----------:|
| Lowering (Leg 1) | ~96 | 41% |
| Pass obligations (ssa/wf) | ~50 | 21% |
| Pass proofs (semantic) | ~35 | 15% |
| Shared pass infra | ~14 | 6% |
| Codegen (Leg 3) | ~13 | 6% |
| E2E composition | ~5 | 2% |
| Venom core (mem) | ~2 | 1% |
| Analysis (base_ptr, mem_alias) | ~7 | 3% |
| Other (semantics typecheck) | ~1 | <1% |

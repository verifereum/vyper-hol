# Compiler definition parity checklist

This document tracks whether the HOL compiler definitions match the intended upstream Python/Vyper compiler implementation.

## Target upstream version

**Target commit:** TBD

Candidate targets observed during cleanup:

- `v0.5.0a3` — latest tag visible in `~/vyper` at audit time.
- `751931ff6` — `upstream/master` / local `master` at audit time, with local branch reported as ahead of `origin/master` by 26 commits.

Recommended policy: pin an exact upstream commit before major proof repair. Avoid targeting a moving branch name such as `master` without recording the commit hash.

## Current upstream anchors recorded in HOL files

The current formalization appears to have been ported from multiple upstream commits, not a single uniform target.

| HOL area/file | Recorded upstream anchor | Notes |
|---|---|---|
| `lowering/defs/exprLoweringScript.sml` | `vyperlang/vyper@6a3248028` | remove `fix_memlocs` pass, #4896 |
| `lowering/defs/contextScript.sml` | `vyperlang/vyper@e1dead045` | sunset GEP, #4895 |
| `lowering/defs/vyperCompilerScript.sml` | `vyperlang/vyper@a7f7bf133` | split algebraic/affine passes |
| `lowering/defs/selectorDispatchScript.sml` | `vyperlang/vyper@a7f7bf133` | selector dispatch definitions |
| `lowering/vyperLoweringCorrectScript.sml` | `vyperlang/vyper@a7f7bf133` | top-level lowering correctness statement |
| `venom/compiler/venomPipelineScript.sml` | `vyperlang/vyper@a7f7bf133` | optimization pipeline definition |
| `venom/codegen/defs/*` | mostly `vyperlang/vyper@e1dead045` | codegen/asm/stack-plan definitions |

## Recent upstream commits likely relevant to parity

Recent `~/vyper` history at audit time included Venom/compiler fixes such as:

| Commit | Summary |
|---|---|
| `751931ff6` | `fix[ux]: panic explicitly in safe_pow() for two-variable case (#5134)` |
| `0744d5d03` | `fix[venom]: apply write effects of multi-output instructions in CSE (#5096)` |
| `a2d8170b5` | `perf[venom]: fast path for empty dynarray assignment (#5097)` |
| `ca838362b` | `fix[venom]: do not coalesce gas reads in CSE (#5083)` |
| `16763a911` | `fix[venom]: reject abi_encode with no arguments (#5092)` |
| `f3209160b` | `fix[venom]: do not elide self-overlapping mcopy (#5087)` |

These should be checked against the formal lowering/pass/codegen definitions if the chosen target commit includes them.

## Parity checklist

Status vocabulary:

- **unknown** — not audited against target commit yet.
- **matches target** — audited and matches target Python behavior.
- **needs update** — HOL definition differs and should be changed.
- **intentional difference** — HOL intentionally abstracts or differs; document why.
- **blocked** — cannot audit until target commit or upstream behavior is clarified.

### Lowering definitions

| HOL file | Likely Python source area | Current anchor | Target status | Notes |
|---|---|---|---|---|
| `lowering/defs/compileEnvScript.sml` | compiler/codegen environment setup | not recorded in header | unknown | Check env/state fields against current lowering implementation. |
| `lowering/defs/contextScript.sml` | `codegen_venom/context`-like helpers | `e1dead045` | unknown | Memory/storage/context helper parity. |
| `lowering/defs/emitHelperScript.sml` | Venom builder/emission helpers | not recorded in header | unknown | Check fresh ids, labels, block emission conventions. |
| `lowering/defs/exprLoweringScript.sml` | expression lowering | `6a3248028` | unknown | High priority; expression semantics proofs depend on this. |
| `lowering/defs/stmtLoweringScript.sml` | statement lowering | header references Python stmt.py but no commit | unknown | High priority; if/for/return/assert lowering may drift. |
| `lowering/defs/moduleLoweringScript.sml` | module/function/dispatch lowering | not recorded in visible header | unknown | Selector dispatch, constructor/deploy code, args/kwargs. |
| `lowering/defs/abiEncoderScript.sml` | ABI encode/decode helpers | not recorded in visible header | unknown | Check recent `abi_encode` behavior, including empty-argument rejection. |
| `lowering/defs/builtin*.sml` | builtin lowering modules | varied/no explicit commit | unknown | raw calls, create, hashing, math, bytes, system, misc, ABI builtins. |
| `lowering/defs/vyperCompilerScript.sml` | top-level lowering/compiler wrapper | `a7f7bf133` | unknown | Check pipeline selection and bytecode assembly path. |

### Venom pipeline/pass definitions

| HOL file/area | Likely Python source area | Current anchor | Target status | Notes |
|---|---|---|---|---|
| `venom/compiler/venomPipelineScript.sml` | optimization levels / pass pipeline | `a7f7bf133` | unknown | Check O2/O3/Os pass lists and pass ordering. |
| `venom/passes/*/defs/*` | individual Venom optimization passes | varies | unknown | Several upstream Venom fixes likely affect pass definitions. |
| `venom/passes/common/shared defs` | shared pass utilities | varies | unknown | Check SSA/WF assumptions and utility behavior. |
| CSE definitions | CSE pass | unknown | unknown | Must check `apply write effects of multi-output instructions in CSE` and `do not coalesce gas reads`. |
| memory copy elision definitions | MCE pass | unknown | unknown | Must check `do not elide self-overlapping mcopy`. |

### Codegen definitions

| HOL file | Likely Python source area | Current anchor | Target status | Notes |
|---|---|---|---|---|
| `venom/codegen/defs/stackModelScript.sml` | stack model | `e1dead045` | unknown | Check stack order conventions carefully. |
| `venom/codegen/defs/stackPlanTypesScript.sml` | stack plan state/types | `e1dead045` | unknown | Spill allocator and labels. |
| `venom/codegen/defs/stackPlanOpsScript.sml` | stack reorder/spill/dup/swap ops | `e1dead045` | unknown | Historical operand-order issue was documented in archived counterexamples. |
| `venom/codegen/defs/stackPlanGenScript.sml` | Venom-to-assembly plan generation | `e1dead045` | unknown | High priority for codegen proof repair. |
| `venom/codegen/defs/planExecScript.sml` | stack-op-to-asm lowering | `e1dead045` | unknown | Check opcode emission. |
| `venom/codegen/defs/asmIRScript.sml` | assembly IR | `e1dead045` | unknown | Data sections, labels, opcode names. |
| `venom/codegen/defs/asmSemScript.sml` | asm interpreter model | `e1dead045` | unknown | May intentionally differ from Python; document abstraction. |
| `venom/codegen/defs/symbolResolveScript.sml` | assembly/symbol resolution | `e1dead045` | unknown | Check symbol size and label offset behavior. |
| `venom/codegen/defs/codegenScript.sml` | top-level codegen composition | `e1dead045` | unknown | Check data-section and bytecode output path. |

### Evaluation fixtures

| HOL file | Purpose | Target status | Notes |
|---|---|---|---|
| `lowering/defs/evalCompilerScript.sml` | executable compile smoke tests | unknown | Should be regenerated/updated after parity changes. |
| `lowering/defs/evalCompilerBytecodeScript.sml` | compare output against bytecode fixtures | unknown | Bytecode fixtures may change after parity update. |

## Suggested parity workflow

1. Choose target upstream commit.
2. Record exact commit here and in relevant source headers when files are updated.
3. For each HOL definition file, compare against Python source at the target commit.
4. Update HOL definitions where needed.
5. Mark intentional abstractions explicitly in file headers and this checklist.
6. Re-run executable compiler/evaluation fixtures and update bytecode fixtures if appropriate.
7. Only then prioritize proving or repairing correctness theorems.

## Open questions

- Should the formalization target a release tag such as `v0.5.0a3`, or a newer exact upstream commit?
- Should all compiler definition files be normalized to a single target commit in their headers?
- Which upstream Venom bug fixes affect theorem statements vs only definitions?
- Are any HOL definitions intentionally simplified compared with Python for proof tractability?

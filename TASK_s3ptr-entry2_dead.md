# TASK: S3 entry seam: the body's dead bytes are the call's

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/entryPtrSeamDeadScript.sml

## Theorem Statement (FROZEN)

1 theorem, currently `cheat` in `lowering/entryPtrSeamDeadScript.sml`. Prove it. Copy of the statement as it stands in the source:

```sml
Theorem external_call_dead_initial_cx:
  !orc am tx.
    external_call_dead tx (call_external orc [] am tx) =
    cx_dead (initial_evaluation_context am.sources am.layouts tx NONE)
```

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

## Completion Criteria

1. `holbuild -j4 build entryPtrSeamDeadTheory` passes with `external_call_dead_initial_cx` proved: no `cheat` in `lowering/entryPtrSeamDeadScript.sml` nor in any theory this run adds, and no FAILs.
2. Nothing in `lowering/loweringPtrCorrectScript.sml` or the other `lowering/entryPtrSeam*Script.sml` files changes.
3. No duplicate or near-duplicate lemmas; helpers in their most general form.

**If the theorem is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build entryPtrSeamDeadTheory
```

Run from the project root (the directory holding `holproject.toml` and this file).

## Background

S3 says the lowered Vyper unit's raw Venom run satisfies the pointer discipline and keeps taint within the source call's dead bytes. Its entry theorem `external_entry_reaches_body_ptr` (in `lowering/loweringPtrCorrectScript.sml`) is now proved from five seams, each its own theory with one `cheat`ed theorem: `entryPtrSeamDead` (the body's dead bytes are the call's), `entryPtrSeamPrefix` (selector dispatch and passing entry checks), `entryPtrSeamRegister` (argument registration reaches the body's start with the S1 relation and the ghost), `entryPtrSeamDecoder` (the pointer-safe calldata decoder contract for every coherent type) and `entryPtrSeamBulk` (its bulk-copy dynamic-array case). This task proves one of them.

A pointer-safe run (`ptr_safe_run`/`ptr_safe_blocks`, `venom/compiler/ptrSafeRunScript.sml`) checks each executed instruction against `ptr_inst_ok` while threading a ghost: provenance `G` (pointer variable -> base, size) and taint `tn` (tainted variables and memory, storage, transient bytes). The judgments in `lowering/bodyPtrDefsScript.sml` (`ptr_covers`, `ghost_inv`, `mem_agree_outside`, `cx_dead`, ...) are the pointer twins of S1's. The selector dispatch and the entry checks touch no memory; the argument decode writes only the parameters' buffers (ALLOCAs whose provenance the ghost records), from calldata, so untainted.

This seam: The entry's run is checked against `external_call_dead` of the source call's result; the body's run, and `ghost_inv`, against `cx_dead` of the call's initial evaluation context. A runtime call leaves the abstract machine's `sources` and `layouts` unchanged, so these coincide.

## Domain Constraints

- Build with holbuild only (no Holmake). The tactic timeout is the project default, 2.5 s per step; don't raise it, and pass no timeout flags.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Don't edit proven statements in other theories, and don't change any definition (in particular nothing in `lowering/defs/`, `venom/`, `lowering/bodyPtrDefsScript.sml`, `lowering/bodyMemoryDefs*`). Don't add axioms or new `cheat`s. No `let` in theorem statements.
- Leave `lowering/loweringPtrCorrectScript.sml` alone: its theorems (`external_entry_reaches_body_ptr`, `external_entry_value_revert_ptr`, `external_frame_ret_ok_ptr`, `body_stmts_sim_ptr` and the rest) are not this task's; don't prove, restate or edit them. Don't edit the other `entryPtrSeam*Script.sml` files either.
- New helper lemmas go in new theories under `lowering/` named for what they prove, or in this seam's own theory file. A new theory must be an ancestor of this seam's theory so its build reaches it. You may use and extend the lane's proved helper theories (`lowering/*PtrScript.sml` and their ancestors); a restated variant of one of them gets a new name, its original stays.
- The named admissions already in the tree may be used as given: S1's in `lowering/loweringRuntimeCorrectScript.sml`, and nothing else (this seam needs no admission). Don't prove, restate or weaken them.
- Commit only proof sources (no task/state/plan/log files). Commit trailer: `Bot: opus (Claude Opus 5.5)`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| this seam | lowering/entryPtrSeamDeadScript.sml | the frozen statement, with hints as comments above it |
| the composer | lowering/loweringPtrCorrectScript.sml | how `external_entry_reaches_body_ptr` consumes the seams (read only) |
| ptr judgments | lowering/bodyPtrDefsScript.sml | cx_dead, mem_agree_outside, ptr_covers, return_buf_ptr, stor_taint_ok, ghost_inv |
| pointer-safe runs | venom/compiler/ptrSafeRunScript.sml | ptr_inst_ok, ptr_safe_run/blocks, ghost_run, fuel lemmas |
| pointer discipline | venom/compiler/ptrDisciplineScript.sml | access_ok, taint_ok, step_prov/step_taint, entry_taint, allocas_from, ctx_has_dalloca |
| source call | semantics/vyperInterpreterScript.sml | call_external, call_external_function, initial_evaluation_context, abstract_machine_from_state, finalize_pending_deletions |
| external_call_dead | lowering/vyperLoweringCorrectScript.sml | the entry's dead bytes |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml, venom/defs/venomStateScript.sml | step_inst, run_from, state |

## Notes

- Hints for this seam are SML comments above its statement; they are not binding.
- Build with `-j4` at most; never `holbuild run`/`repl`.

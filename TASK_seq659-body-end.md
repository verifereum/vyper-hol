# TASK: S3: falling off the end of the guarded body is memory-safe

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/loweringMemCorrectScript.sml

## Theorem Statement (FROZEN)

One theorem, currently `cheat` in `lowering/loweringMemCorrectScript.sml`.
Prove it. Copy of each statement as it stands in the source:

```sml
Theorem compile_guarded_body_end_mem_safe:
  !ctx cenv nkey ut iv stmts rt st x st' sb fn s.
    compile_guarded_body cenv F nkey ut iv stmts rt st = (x, st') /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' fn /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    !fuel. mem_safe_run fuel ctx fn s /\ (!e. run_from fuel ctx fn s <> Error e)
```

**Do not modify these statements.** Prove them as-is, or produce a
counterexample.

## Completion Criteria

1. `holbuild -j4 build loweringMemCorrectTheory` passes with the theorem
   above proved (no `cheat` in its proof) and no FAILs.
2. The only `cheat`s left in `lowering/loweringMemCorrectScript.sml` are the
   four named admissions `body_stmts_sim_mem`,
   `external_entry_value_revert_mem`, `external_entry_reaches_body_mem` and
   `external_frame_ret_ok_mem`, unchanged, and `lower_vyper_runtime_unit_run_mem_safe` (proved by a separate run). Don't prove,
   restate, weaken or add to the admissions.
3. No `cheat` in `lowering/entryHaltMemScript.sml` (all its theorems are
   proved already; don't change them).
4. No duplicate or near-duplicate lemmas; helpers in their most general form.

**If a theorem is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build loweringMemCorrectTheory
```

Run from the project root (the directory holding `holproject.toml` and this
file).

## Background

S3 says the lowered Vyper unit's raw Venom run is memory-safe: every
instruction executed reads and writes memory below the allocation frontier
(`vs_alloca_next`), except the revert-forwarding pair after a failed call
(`revert_forward_at`, see `venom/compiler/unitTransformDefsScript.sml` and
`mem_safe_block` in `venom/compiler/memSafeRunScript.sml`).

`lower_vyper_runtime_unit_run_mem_safe` is composed like S1:
`lower_vyper_runtime_unit_correct` and `lower_vyper_runtime_unit_body` in
`lowering/loweringRuntimeCorrectScript.sml` are the template. The entry
either reverts on the call value (`external_entry_value_revert_mem`) or
reaches the body (`external_entry_reaches_body_mem`, which gives the body's
start state including `stmt_state_rel` and `alloca_history func s0`, and
reduces the run from `__entry` to a memory-safe run from `s0`). The body
runs by `body_stmts_sim_mem` at `d = NONE` with `RetQ = (\v es r. T)` and
`external_frame_ret_ok_mem`; it either exits or lands at its end, where
`compile_guarded_body_end_mem_safe` applies. The four named admissions are
the memory twins of S1's admissions and are assumed. S1's own admissions in
`loweringRuntimeCorrect` (`external_body_frame`, `external_body_source_ok`,
...) may also be used.

The body judgments (`stmt_frag_mem`, `expr_sim_mem`) carry the antecedent
`res <> INR (Error (RuntimeError "convert empty bytes to signed"))` on the
source result. The composition discharges it from S3's premise
`~source_exempt tops (call_external ...)`: `source_exempt` covers exactly
that error (`unspecified_behaviour_exempt`), and the body's error result
becomes `call_external`'s result the way S1 relates them. Do not add a
premise for it.

The `mem_safe_blocks` goal is for every fuel, including out-of-fuel and
error prefixes; `mem_safe_run_all_fuel` and `frag_exec_mem_complete` in
`fragExecMemScript.sml` bridge `frag_exec_mem`'s non-error continuations to
all fuel.

## Domain Constraints

- Build with holbuild only (no Holmake). The tactic timeout is the project
  default, 2.5 s per step; don't raise it.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with
  `>~`, `>-`, `>|`.
- Don't edit proven statements in other theories. Don't add axioms or new
  `cheat`s. New helper lemmas go in `entryHaltMemScript.sml` or
  `loweringMemCorrectScript.sml`, or in the theory they naturally belong
  to, if it's under `lowering/`.
- No `let` in theorem statements.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| frag_exec_mem, run_inst_seq_mem_ok, mem_safe_run_all_fuel, frag_exec_mem_complete, revert_forward_frag_mem, stop_frag_mem, frag_exec_mem_step, frag_exec_mem_run_inst_seq | lowering/fragExecMemScript.sml | memory-safe fragment judgment and rules |
| mem_safe_step/block/blocks/run, mem_safe_run_step, mem_safe_run_head, fuel monotonicity | venom/compiler/memSafeRunScript.sml | memory-safe runs |
| inst_mem_below_frontier, revert_forward, inst_mem_ok_in_fn | venom/compiler/unitTransformDefsScript.sml | frontier check |
| below_frontier_MSTORE, _MCOPY, _RETURN, ... | lowering/instMemFrontierScript.sml | per-opcode frontier forms |
| alloca_site_cases, step_alloca_site, alloca_site_frontier, return_buffer_mem_safe, compile_alloc_buffer_mem_ok, compile_alloc_buffer_frag_mem, compile_keccak256_word_mem_ok, emit_*_mem_ok | lowering/allocaFootprintScript.sml | ALLOCA buffer footprint leaves (template style) |
| return sequences, return_word_run, return_copy_run, *_parts, step_alloca_frame | lowering/loweringHaltScript.sml | the non-memory halt proofs |
| entry_decode_arg_run, entry_decode_arg_frame | lowering/entryArgPtrsScript.sml | the non-memory decode proofs |
| compile_decode_static_arg_calldata, compile_decode_word_arg_calldata | lowering/entryDecodePlanPropsScript.sml | decode simulations |
| static_dec, dec_frame, dec_run, decode_static_buf_run | lowering/abiDecodeStaticPropsScript.sml | static decode machinery |
| stmt_frag_mem, frame_ret_ok_mem, return_buf_frame, expr_sim_mem | lowering/bodyMemoryDefsScript.sml | body memory judgments (now with `alloca_history` and the empty-bytes guard) |
| alloca_history, alloca_history_empty, alloca_history_callee_entry | venom/proofs/allocaHistoryScript.sml | allocation-history invariant |
| entry/halt memory leaves (all proved) | lowering/entryHaltMemScript.sml | compile_return_none_external_frag_mem, compile_guarded_body_stop_frag_mem, compile_external_return_*_frag_mem, entry_decode_arg_mem_ok |
| source_exempt, unspecified_behaviour_exempt | lowering/e2eDefsScript.sml | the only exemption; covers RuntimeError "convert empty bytes to signed" |
| S1 composition and admissions; guarded_body_code, guarded_body_stmts_env | lowering/loweringRuntimeCorrectScript.sml | template for the composition |
| compile_guarded_body_def, compile_register_positional_args_def | lowering/defs/moduleLoweringScript.sml | lowering definitions |
| exec_alloca_def, step_inst_base (INVALID, STOP) | venom/defs/venomExecSemanticsScript.sml | Venom semantics |
| alloca_next_valid | venom/defs/venomMemDefsScript.sml | alloca invariant |

## Notes

- Scope: only `compile_guarded_body_end_mem_safe`. Leave every other cheat in the file alone; a separate run proves `lower_vyper_runtime_unit_run_mem_safe`.

- A statement check (by reading) judged both provable against the earlier
  body judgments. The body judgments since gained the `alloca_history`
  conjuncts and the empty-bytes guard; the composition's own statement is
  unchanged.
- `compile_guarded_body_end_mem_safe`: falling off the end emits STOP, or
  INVALID for a function with a return type (no lock in this F case); neither
  touches memory.

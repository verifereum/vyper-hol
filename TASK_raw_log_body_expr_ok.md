# TASK: raw_log body-induction case (raw_log_body_expr_ok)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (the directory holding holproject.toml); the theorem is the last one in lowering/bodySimCallRawLogScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem raw_log_body_expr_ok:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`body_expr_ok` and `body_exprs_ok` are defined in lowering/bodySimScript.sml
(~176); `expr_sim` and `expr_vv_sim` in lowering/exprSimDefsScript.sml
(over `gas_outcome`, lowering/gasOutcomeScript.sml).
`body_expr_ok_intro` (lowering/bodySimExprCasesScript.sml) reduces the goal
to operands containing an internal call (`int_calls_expr e <> []`).

## Completion Criteria

1. `holbuild -j4 build bodySimCallRawLogTheory bodySimCallCasesTheory` passes and `raw_log_body_expr_ok` is proved. The only cheat allowed in the raw_log files is the held admission `raw_log_make_array_children_ok` (see below); no other cheat in the target or any helper you add. (Ancestor theories outside the raw_log files have admitted proofs in this worktree; those inherited admissions are expected.)
2. No duplicate or near-duplicate lemmas; reuse existing ones rather than restating them. Helpers used only here are `[local]`.
3. Files you may edit: lowering/bodySimCallRawLogScript.sml, lowering/bodySimRawLogScript.sml (only bodySimCallRawLog imports it), and new theories `lowering/bodySimRawLog*Script.sml` that only these import. lowering/exprSimRawLogScript.sml is frozen (another proof imports it; it builds now): do not edit it. Edit no other existing file: no change to any other theorem, to any definition, or to anything under semantics/, lowering/defs/ or venom/defs/. If you believe you need such a change, stop and report it (blocked) with the reason.
4. `raw_log_make_array_children_ok` in lowering/bodySimCallRawLogScript.sml is a deliberately held admission: keep its statement and its `cheat` exactly as they are, and use it for the topic elements of the MakeArray operand.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, do not weaken the statement.

## Build

```
holbuild -j4 build bodySimCallRawLogTheory bodySimCallCasesTheory
```

## Background

`raw_log(topics, data)` with `topics` a literal `DynArray[bytes32, n]`
(n <= 4, a `MakeArray` builtin) and `data` either `bytes32` or a
`Bytes[N]` memory value. The lowering is compile_call's RawLog clause
(lowering/defs/exprLoweringScript.sml ~2795, raw_log_topic_exprs_def
~2627): the topic words via lower_word_args, then the data (bytes32: a
32-byte buffer written with MSTORE; Bytes: MLOAD of its length and +32
for its data), then `LOG n` with the topics reversed. The source is
eval_expr's `Call _ RawLog` clause (semantics/vyperInterpreterScript.sml
~1675): both operands, at most 4 topics, check_not_static, push_log.

In the body case the operands may contain internal calls; the topic
elements' and data's simulations come from `body_exprs_ok cx es`
(the MakeArray's elements through `raw_log_make_array_children_ok`).

Static frames: Venom's LOG aborts when `vs_call_ctx.cc_static`, and the
source raises in a static context; `state_rel_def` gives both
`~cx.txn.is_static` and `~s.vs_call_ctx.cc_static`, so stmt_state_rel
rules the static case out. exprSimRawLog's raw_log_core_step,
raw_log_step, raw_log_words_step and raw_log_source_eval carry those
premises.

### Starting point

lowering/bodySimRawLogScript.sml and the lemmas above the target in
lowering/bodySimCallRawLogScript.sml (raw_log_dynamic_frag,
raw_log_fixed32_body_frag) hold a complete proof of this case from an
older base. It predates two infrastructure changes:

- counted GAS: `expr_sim` is now stated with `gas_outcome` and a
  `gas_admissible` precondition instead of `frag_exec`. Commit b61437ec3
  ("Port the hash builtin simulations to counted gas",
  lowering/exprSimHashScript.sml) ported a similar memory-reading
  builtin to it: `expr_sim_suffix`, `hash_run_path`, `hash_abort_path`
  show the pattern.
- `expr_body_pre` / `expr_sim_pre` gained conjuncts, and the old
  `exprSim` theory was split (exprSimDefs, exprSimHypsDefs, exprSimSource,
  exprSimStack, loweringPosts and others).

Port it: adapt the existing lemmas to the current definitions rather
than starting over.

## Domain Constraints

- holbuild only; build at most -j4. The per-step tactic timeout stays at its default.
- No `TRY`/`ORELSE` around search tactics (metis_tac etc.).
- Do not touch the frozen statement, the held admission, or any file outside the editable set above.

## Available Resources

- lowering/bodySimCallCasesScript.sml: consumes raw_log_body_expr_ok.
- lowering/bodySimExprCasesScript.sml, lowering/bodySimCallRawCallScript.sml, lowering/bodySimCallRawRevertScript.sml: other body cases.
- lowering/exprSimHashScript.sml, lowering/exprSimPrecompilesScript.sml, lowering/exprSimWordArgsScript.sml: counted-GAS ports of comparable builtin cases.
- lowering/gasOutcomeScript.sml, lowering/fragGas*Script.sml, lowering/fragExecScript.sml: the gas_outcome / frag machinery.
- lowering/stmtSimLogEmitScript.sml: the `log` statement's LOG emission under the current interface.

## Notes

Ancestors of the raw_log files with admitted (cheated) proofs in this
worktree are a local overlay hidden from git; never edit or commit them.
The expression case (raw_log_expr_vv_ok) is proved by a separate run in
another worktree; don't work on it.
In this worktree lowering/exprSimCallRawLogScript.sml is a local stub
(its theorem admitted, hidden from git) so the consumer build reaches
bodySimExprCases and bodySimCallCases; the real proof is the separate
run's. It now builds; don't edit it.

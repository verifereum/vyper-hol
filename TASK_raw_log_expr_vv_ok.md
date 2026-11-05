# TASK: raw_log expression simulation (raw_log_expr_vv_ok)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (the directory holding holproject.toml); the theorem is the last one in lowering/exprSimCallRawLogScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem raw_log_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawLog) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawLog) args dflt)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`expr_vv_ok`, `expr_sim_below` and `expr_sim_pre` are defined in
lowering/exprSimHypsDefsScript.sml; `expr_sim` and `expr_vv_sim` in
lowering/exprSimDefsScript.sml (over `gas_outcome`, lowering/gasOutcomeScript.sml).

## Completion Criteria

1. `holbuild -j4 build exprSimCallRawLogTheory exprSimCallsTheory` passes and `raw_log_expr_vv_ok` is proved, with no cheat in it or in any helper lemma you add. (Ancestor theories outside the raw_log files have admitted proofs in this worktree; those inherited admissions are expected and are not your concern.)
2. No duplicate or near-duplicate lemmas; reuse existing ones rather than restating them. Helpers used only here are `[local]`.
3. Files you may edit: lowering/exprSimCallRawLogScript.sml, and new theories `lowering/exprSimRawLogSim*Script.sml` that only exprSimCallRawLog imports. lowering/exprSimRawLogScript.sml is weakly frozen: it builds now and another proof imports it, so you may add lemmas to it but not change or delete the existing ones. Edit no other existing file: no change to any other theorem, to any definition, or to anything under semantics/, lowering/defs/ or venom/defs/. If you believe you need such a change, stop and report it (blocked) with the reason.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, do not weaken the statement.

## Build

```
holbuild -j4 build exprSimCallRawLogTheory exprSimCallsTheory
```

## Background

`raw_log(topics, data)` with `topics` a literal `DynArray[bytes32, n]`
(n <= 4, a `MakeArray` builtin) and `data` either `bytes32` or a
`Bytes[N]` memory value. The lowering is compile_call's RawLog clause
(lowering/defs/exprLoweringScript.sml ~2795, with raw_log_topic_exprs_def
~2627): the topic words via lower_word_args, then the data (bytes32: a
32-byte buffer written with MSTORE; Bytes: MLOAD of its length and +32
for its data), then `LOG n` with the topics reversed. The source is
eval_expr's `Call _ RawLog` clause (semantics/vyperInterpreterScript.sml
~1675): it evaluates both operands, checks at most 4 topics,
check_not_static, and push_log (encode_raw_event_values ...).
Typing: well_typed_expr's RawLog clause
(semantics/type/vyperTypeSystemScript.sml ~821).

Static frames: Venom's LOG aborts when `vs_call_ctx.cc_static`, and the
source raises in a static context; `state_rel_def` gives both
`~cx.txn.is_static` and `~s.vs_call_ctx.cc_static`, so stmt_state_rel
rules the static case out. lowering/exprSimRawLogScript.sml already
carries `~...static` premises on raw_log_core_step, raw_log_step,
raw_log_words_step and raw_log_source_eval for this.

### Starting point

lowering/exprSimCallRawLogScript.sml holds a complete proof (~870 lines,
26 theorems) of this statement from an older base, and
lowering/exprSimRawLogScript.sml its shared helpers (these build now).
The old proof predates two infrastructure changes and fails from its
second theorem (`raw_log_child_pre`) on:

- counted GAS: `expr_sim` is now stated with `gas_outcome` and a
  `gas_admissible` precondition instead of `frag_exec`. Commit b61437ec3
  ("Port the hash builtin simulations to counted gas",
  lowering/exprSimHashScript.sml) ported a similar memory-reading
  builtin (keccak256) to it: `expr_sim_suffix`, `hash_run_path`,
  `hash_abort_path` show the pattern.
- `expr_sim_pre` gained conjuncts (ABI-decode target closure among them),
  and the old `exprSim` theory was split (exprSimDefs, exprSimHypsDefs,
  exprSimSource, exprSimStack, loweringPosts and others).

Port it: adapt the existing lemmas to the current definitions rather
than starting over.

## Domain Constraints

- holbuild only; build at most -j4. The per-step tactic timeout stays at its default.
- No `TRY`/`ORELSE` around search tactics (metis_tac etc.).
- Do not touch the TASK file's frozen statement or any file outside the editable set above.

## Available Resources

- lowering/exprSimCallsScript.sml: consumes raw_log_expr_vv_ok as compile_raw_log_sim.
- lowering/exprSimHashScript.sml, lowering/exprSimPrecompilesScript.sml, lowering/exprSimWordArgsScript.sml: counted-GAS ports of comparable builtin cases.
- lowering/gasOutcomeScript.sml, lowering/fragGas*Script.sml, lowering/fragExecScript.sml: the gas_outcome / frag machinery.
- lowering/stmtSimLogEmitScript.sml: the `log` statement's LOG emission under the current interface.

## Notes

Ancestors of the raw_log files with admitted (cheated) proofs in this
worktree are a local overlay hidden from git; never edit or commit them.

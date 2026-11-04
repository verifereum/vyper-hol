# TASK: raw_call expression simulation (compile_raw_call_case)

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root (the directory holding holproject.toml); the theorem is in lowering/exprSimRawCallScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_raw_call_case:
  !nocalls ctx func cenv cx ann flags args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`expr_sim_case`, `expr_vv_case` and `exprs_case` are defined in
lowering/exprSimHypsScript.sml (lines ~465-500). Its two users,
`compile_raw_call_sim` (lowering/exprSimCallsScript.sml) and
`body_raw_call_case` (lowering/bodySimExprCasesScript.sml), are already
proved from it; do not change them.

## Completion Criteria

1. `holbuild -j4 build exprSimRawCallTheory exprSimCallsTheory bodySimExprCasesTheory` passes and `compile_raw_call_case` is proved (no cheat in it or in any helper it uses).
2. No duplicate or near-duplicate lemmas; reuse the existing ones listed below rather than restating them. Helpers used only here are `[local]`.
3. New helper lemmas go in lowering/exprSimRawCallScript.sml (or a new lowering/exprSimRawCall*Script.sml theory registered like the others). Do not change the statement of any existing theorem or any definition under semantics/, lowering/defs/ or venom/defs/. You may export a lemma that is currently `[local]` (e.g. `state_rel_adopt_consume` in extCallOracleStep) and add `Ancestors`.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, do not weaken the statement.

## Build

```
holbuild -j4 build exprSimRawCallTheory exprSimCallsTheory bodySimExprCasesTheory
```

## Background

`raw_call(to, data, value=, gas=, max_outsize=, is_static_call=, revert_on_failure=)`
lowers (compile_call's RawCallTarget clause, lowering/defs/exprLoweringScript.sml ~2611)
to: the address via lower_value, the data (a `Bytes[N]` memory value),
the value=/gas= keyword operands in source order (compile_ext_call_kwargs),
GAS when no gas=, the output buffer (compile_raw_call_outbuf), and the
call plus revert/ok split (compile_raw_call_finish,
lowering/defs/builtinSystemScript.sml).

The source (eval_raw_call, semantics/vyperInterpreterScript.sml ~941), in
oracle mode (`IS_SOME st.outcomes`) and non-delegate, takes its outcome
with take_call_outcome and adopts it on success when not static
(adopt_call_outcome), the same oracle the lowered CALL/STATICCALL reads
(exec_ext_call_oracle_step). `expr_body_pre` excludes delegate raw_calls
and raw_calls without revert_on_failure (`~expr_has_evm_run`, via
`expr_evm_run_root` in lowering/supported/supportedExprTraverseScript.sml),
so those cases hold vacuously.

Typing: `raw_call_typed_data_dynamic`
(semantics/prop/vyperRawCallDataDomainScript.sml) gives that the data
operand has type `BaseT (BytesT (Dynamic n))`; without it the theorem is
false (a bytesN word would be read as a memory pointer).

The sibling `compile_raw_call_calldata_case` (raw_call of msg.data) is
being proved separately in parallel; it is not available here. Shared
machinery you write for the CALL tail should be general (parametric in
the data pointer and length), since it serves both.

## Domain Constraints

- Read `AGENTS.md` at the project root first; it wins.
- holbuild only; never raise the 2.5 s per-step tactic timeout or pass `--tactic-timeout`. A slow step is a proof bug: split it or cut the simp set.
- Never wrap `metis_tac` or any search tactic in `TRY`/`ORELSE`/`FIRST`; select goals with `>~`, `>-`, `>|`.
- No `cheat` of your own, no new axioms, no `g`/`e` interactive sessions, no `holbuild run`/`repl`.
- Proofs ≤ ~50 lines each; split into helper lemmas.
- Commit messages end with the trailer lines:
  `Bot: opus (Claude Opus 5.5)` and `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | lowering/exprSimRawCallScript.sml | `compile_raw_call_case` (cheat). |
| Case predicates | lowering/exprSimHypsScript.sml | `expr_sim_case_def`, `expr_vv_case_def`, `exprs_case_def`, `expr_body_pre`, `expr_sim_inv_def`. |
| Closest sibling (proved) | lowering/exprSimSendScript.sml | `compile_send_case`, `send_expr_sim`, `take_call_outcome_typed`: send's CALL through the oracle, same case-lemma shape. |
| Oracle call step | lowering/extCallOracleStepScript.sml | `exec_ext_call_oracle_step`, `venom_call_request_source`, `state_rel_adopt_consume` (local), `logs_rel_eq`, `local_ptrs_rel_oracle_fields`, `send_call_oracle_step`. |
| Bytes operand + STATICCALL + return buffer | lowering/exprSimHashScript.sml | sha256 lowering: `hash_data_prefix_run`, `sha256_tail_run`, `sha256_tail_frame`, `hash_write_memory_disjoint`, `hash_write_memory_read_self`, `hash_returndata_state_rel`, `typed_bytes_prefix`, `expr_val_rel_memory`, `expr_val_at_footprint`, `hash_alloc_mstore_frame`. |
| Operand bookkeeping | lowering/exprSimOperandsScript.sml | `expr_post_operand_kept*`, `fresh_not_local_ptr`, `alloca_clear_of_locals`. |
| JNZ / new_block control flow under frag_exec | lowering/exprSimIfExpScript.sml | how a two-block split is run. |
| Lowering defs | lowering/defs/exprLoweringScript.sml, lowering/defs/builtinSystemScript.sml | `compile_call` RawCallTarget clause, `compile_ext_call_kwargs_def`, `compile_raw_call_outbuf_def`, `compile_raw_call_finish_def`. |
| Source semantics | semantics/vyperInterpreterScript.sml | `eval_raw_call_def`, `eval_raw_call_preserves_non_accounts`; take_call_outcome / adopt_call_outcome. |
| Typing | semantics/type/vyperTypeSystemScript.sml, semantics/prop/vyperRawCallDataDomainScript.sml | RawCallTarget clause of `well_typed_expr`, `raw_call_kws_ok`, `raw_call_typed_data_dynamic`. |
| Exclusion | lowering/supported/supportedExprTraverseScript.sml | `expr_evm_run_root`. |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | CALL/STATICCALL in oracle mode. |
| Built signatures | .holbuild/ (after a build) | `.sig` files of every ancestor. |

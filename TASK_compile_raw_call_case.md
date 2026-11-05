# TASK: raw_call expression simulation (compile_raw_call_case)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
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
lowering/exprSimHypsDefsScript.sml (~line 183). Its two users,
`raw_call_expr_vv_ok` (lowering/exprSimCallRawCallScript.sml) and
`raw_call_body_expr_ok` (lowering/bodySimCallRawCallScript.sml), are
already proved from it; do not change them.

## Completion Criteria

1. `holbuild -j4 build exprSimRawCallTheory exprSimCallRawCallTheory bodySimCallRawCallTheory` passes and `compile_raw_call_case` is proved (no cheat in it or in any helper it uses).
2. No duplicate or near-duplicate lemmas; reuse existing ones (listed below) rather than restating them. Helpers used only here are `[local]`.
3. New helper lemmas go in lowering/exprSimRawCallScript.sml or in new theories `lowering/exprSimRawCall*Script.sml` that only exprSimRawCall imports. The one exception: if a lemma you need is `[local]` in lowering/exprSimRawCallCalldataScript.sml or lowering/rawCallFragPathScript.sml, drop its `[local]` there (change nothing else in that file) instead of duplicating it, and list every such export in your final report. Edit no other existing file: no change to any existing theorem, to any definition, or to anything under semantics/, lowering/defs/ or venom/defs/. If you believe you need such a change, stop and report it (blocked) with the reason.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, do not weaken the statement.

## Build

```
holbuild -j4 build exprSimRawCallTheory exprSimCallRawCallTheory bodySimCallRawCallTheory
```

## Background

`raw_call(to, data, value=, gas=, max_outsize=, is_static_call=, revert_on_failure=)`
lowers (compile_call's RawCallTarget clause, lowering/defs/exprLoweringScript.sml ~2736)
to: the address via lower_value, the data (a `Bytes[N]` memory value,
MLOAD for its length and +32 for its data), the value=/gas= keyword
operands in source order (compile_ext_call_kwargs), GAS when no gas=,
the output buffer (compile_raw_call_outbuf), and the call with its result
(compile_raw_call_finish, lowering/defs/builtinSystemScript.sml ~74).

The source (eval_raw_call, semantics/vyperInterpreterScript.sml ~914), in
oracle mode (`IS_SOME st.outcomes`) and non-delegate, takes its outcome
with take_call_outcome and adopts it (adopt_call_outcome), the same
oracle the lowered CALL/STATICCALL reads (exec_ext_call_oracle_step).
Delegate raw_calls are excluded by `expr_body_pre` (`~expr_has_evm_run`,
`expr_evm_run_root` in lowering/supported/supportedExprTraverseScript.sml),
so they hold vacuously. Every other raw_call is in scope, with
`revert_on_failure` true (revert with the callee's returndata on failure;
result nothing or `Bytes[max_outsize]`) and false (result `bool`, or a
`(bool, Bytes[max_outsize])` tuple in a fresh memory buffer).

Typing: the RawCallTarget clause of `well_typed_expr`
(semantics/type/vyperTypeSystemScript.sml) gives that the data operand has
type `BaseT (BytesT (Dynamic n))`; `raw_call_typed_data_dynamic` in the
target file states it.

### Starting point

lowering/exprSimRawCallScript.sml holds a complete proof (~3.7k lines,
95 theorems) of this statement from an older base, on which raw_calls
without revert_on_failure were excluded. Two things changed since:

- The simulation infrastructure moved on (counted GAS observations,
  static frames, the split of `exprSim` into exprSimDefs / exprSimHypsDefs
  / exprSimSource / exprSimStack / loweringPosts and others). The old proof
  fails from its third theorem (`raw_call_kwargs_sim`) on. Port it: adapt
  the existing lemmas to the current definitions rather than starting over.
- raw_calls with revert_on_failure = F are now in scope (the old
  `flags.rcf_revert_on_failure` hypotheses in its helper lemmas no longer
  follow from `expr_body_pre`). Their cases are new work.

The sibling `raw_call` of `msg.data` (RawCallCalldataTarget) is now
proved on the base: lowering/exprSimRawCallCalldataScript.sml
(`compile_raw_call_calldata_case`). It shares compile_raw_call_finish and
the output buffer with this case, and exports the finish-tail lemmas
(listed under Available Resources). Reuse them: add exprSimRawCallCalldata
(and rawCallFragPath) to the Ancestors and replace the old proof's local
copies of the same facts with them, rather than porting duplicates.

The base also changed under the harvest since the last run:
- counted-GAS observations for oracle calls (see exprSimSend's gas
  lemmas and rawCallFragPath's `frag_path_*` judgments);
- `expr_exit (INR (Error (RevertData d))) (Abort a s) <=> a = Revert_abort`;
- `expr_body_pre` adds `IS_SOME (supported_function_decl tops c Internal)`;
- builtin args carry a `~is_extcode` premise;
- `call_result_rel_at gobs` at the top level.

## Domain Constraints

- Read `AGENTS.md` at the project root first; it wins.
- holbuild only; never raise the 2.5 s per-step tactic timeout or pass `--tactic-timeout`. A slow step is a proof bug: split it or cut the simp set.
- Never wrap `metis_tac` or any search tactic in `TRY`/`ORELSE`/`FIRST`; select goals with `>~`, `>-`, `>|`.
- No `cheat` of your own, no new axioms, no `g`/`e` interactive sessions, no `holbuild run`/`repl`.
- Proofs ≤ ~50 lines each; split into helper lemmas.
- Many ancestor theories in this worktree have their proofs admitted locally (uncommitted edits, marked skip-worktree in git). Leave them alone; never stage, commit or revert them. Commit only your own files.
- Commit messages end with the trailer lines:
  `Bot: opus (Claude Opus 5.5)` and `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Calldata sibling (proved, current base) | lowering/exprSimRawCallCalldataScript.sml | `compile_raw_call_calldata_case` and the shared finish-tail lemmas: `raw_call_typed_outcome`, `raw_call_oracle_result`, `raw_call_oracle_step`, `raw_call_outbuf_write_frame`, `raw_call_outbuf_write_contents`, `raw_call_finish_revert_compile`, `raw_call_revert_copy`, `raw_call_revert_run`, `raw_call_revert_frag`, `raw_call_failed_jnz_frag`, `raw_call_cap_run`, `raw_call_output_length_memory`, `precompile_result_length`. Reuse these; don't port local copies. |
| Counted-GAS fragment paths | lowering/rawCallFragPathScript.sml | `frag_path_def` and its rules (`frag_path_seq`, `frag_path_then`, `frag_path_run_inst_seq`, `frag_path_enter`, `frag_path_fresh_label`, `frag_path_abort_suffix`, ...). |
| Target | lowering/exprSimRawCallScript.sml | `compile_raw_call_case` and the old proof's helpers. |
| Case predicates | lowering/exprSimHypsDefsScript.sml, lowering/exprSimHypsScript.sml | `expr_sim_case_def`, `expr_vv_case_def`, `exprs_case_def`, `expr_body_pre`, `expr_sim_inv_def`, `expr_sim_case_of_vv`, `typed_args_ready_of_case`. |
| Closest sibling (proved, current base) | lowering/exprSimSendScript.sml | `compile_send_case`, `send_expr_sim`: send's CALL through the oracle, same case-lemma shape, on the current infrastructure. |
| Oracle call step | lowering/extCallOracleStepScript.sml | `exec_ext_call_oracle_step`, `venom_call_request_source`, `state_rel_adopt_consume`, `send_call_oracle_step`. |
| Bytes operand + call + return buffer | lowering/exprSimHashScript.sml, lowering/exprSimPrecompilesScript.sml, lowering/exprSimECArithScript.sml | precompile STATICCALLs with memory data and return buffers on the current base (oracle success bit). `ecadd_success_bounds`, `ecmul_success_bounds` are exported. |
| Operand bookkeeping | lowering/exprSimOperandsScript.sml, lowering/exprSimWordArgsScript.sml | `expr_post_operand_kept*`, typed word args (`lower_word_args`, `typed_args_post`). |
| JNZ / new_block control flow under frag_exec | lowering/exprSimIfExpScript.sml | how a two-block split is run. |
| Tuple / bytes memory values | lowering/exprSimAggregate*Script.sml, valueEncoding | how a located tuple value relates to memory. |
| Lowering defs | lowering/defs/exprLoweringScript.sml, lowering/defs/builtinSystemScript.sml | `compile_call` RawCallTarget clause, `compile_ext_call_kwargs_def`, `compile_raw_call_outbuf_def`, `compile_raw_call_finish_def`. |
| Source semantics | semantics/vyperInterpreterScript.sml | `eval_raw_call_def`, take_call_outcome / adopt_call_outcome. |
| Typing | semantics/type/vyperTypeSystemScript.sml | RawCallTarget clause of `well_typed_expr`, `raw_call_kws_ok`, `raw_call_return_type`. |
| Exclusion | lowering/supported/supportedExprTraverseScript.sml | `expr_evm_run_root`. |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | CALL/STATICCALL in oracle mode, MCOPY. |

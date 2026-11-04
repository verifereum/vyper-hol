# TASK: raw_call of msg.data, extended to revert_on_failure=False and oracle-answered precompiles (compile_raw_call_calldata_case)

## Meta
Status: in progress (extension after a base change)
Priority: P1
Created: 2026-11-04
Location: project root (the directory holding holproject.toml); the theorem is in lowering/exprSimRawCallCalldataScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_raw_call_calldata_case:
  !nocalls ctx func cenv cx ann flags args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx
      (Call ann (RawCallCalldataTarget flags) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx
      (Call ann (RawCallCalldataTarget flags) args dflt)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`expr_sim_case`, `expr_vv_case` and `exprs_case` are defined in
lowering/exprSimHypsScript.sml (lines ~465-500). Its two users,
`compile_raw_call_calldata_sim` (lowering/exprSimCallsScript.sml) and
`body_raw_call_calldata_case` (lowering/bodySimExprCasesScript.sml), are
already proved from it; do not change them.

## Completion Criteria

1. `holbuild -j4 build exprSimRawCallCalldataTheory exprSimCallsTheory bodySimExprCasesTheory` passes and `compile_raw_call_calldata_case` is proved (no cheat in it or in any helper it uses).
2. No duplicate or near-duplicate lemmas; reuse the existing ones listed below rather than restating them. Helpers used only here are `[local]`.
3. New helper lemmas go in lowering/exprSimRawCallCalldataScript.sml (or a new lowering/exprSimRawCallCalldata*Script.sml theory). Do not change the statement of any existing theorem or any definition under semantics/, lowering/defs/ or venom/defs/. You may export a lemma that is currently `[local]` (e.g. `state_rel_adopt_consume` in extCallOracleStep) and add `Ancestors`.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, do not weaken the statement.

## Build

```
holbuild -j4 build exprSimRawCallCalldataTheory exprSimCallsTheory bodySimExprCasesTheory
```

## Background

**Current state (read first).** The theorem was proved on an older base. This
branch is now one commit on a newer base, and the existing proof in
lowering/exprSimRawCallCalldataScript.sml no longer builds, for two reasons
introduced by the base:

1. `expr_evm_run_root` (lowering/supported/supportedExprTraverseScript.sml) no
   longer excludes raw_calls without `revert_on_failure`. Only delegate
   raw_calls (and creates) are excluded now. So `raw_call(..., revert_on_failure=False)`
   is in scope: the lowering then returns the call's success flag and the
   output instead of reverting (compile_raw_call_finish's non-revert branch),
   and the source returns the matching tuple value (eval_raw_call). The
   existing proof assumed `flags.rcf_revert_on_failure` (first failure at
   `calldata_call_pre`); extend it to cover both values of the flag.
2. Computed precompiles (targets 1, 2, 6, 7 called with value 0) now take
   their success bit from the next oracle outcome on both the source and the
   Venom side (take_outcome / take_call_outcome in extCallOracle and the
   Venom CALL oracle step); on success their data is still
   `precompile_result`'s. Lemmas about take_outcome on precompiles may need
   updating.

`stmt_state_rel` also gained an `immutable_base_zero` conjunct, and
`stmt_state_rel_allocas_frame` a matching premise
(lowering/exprLoweringPropsScript.sml); proofs that rebuild `stmt_state_rel`
need it (see `immutable_base_zero_frame`).

The commit "Apply integration tip repair" on this branch repairs base proofs
outside this task; leave the files it touches alone.


`raw_call(to, msg.data, value=, gas=, max_outsize=, is_static_call=, revert_on_failure=)`
lowers (compile_call's RawCallCalldataTarget clause,
lowering/defs/exprLoweringScript.sml) to: the address via lower_value,
the value=/gas= keyword operands in source order
(compile_ext_call_kwargs), GAS when no gas=, the output buffer
(compile_raw_call_outbuf), a copy of all calldata into a fresh DALLOCA
region at vs_fmp (compile_msg_data_to_memory), the call plus
revert/ok split (compile_raw_call_finish, lowering/defs/builtinSystemScript.sml),
then `SETFMP [data_ptr]`, which gives vs_fmp back.

The source (eval_raw_call, semantics/vyperInterpreterScript.sml), in
oracle mode (`IS_SOME st.outcomes`) and non-delegate, sends
`cx.txn.calldata`, takes its outcome with take_call_outcome and adopts it
on success when not static (adopt_call_outcome), the same oracle the
lowered CALL/STATICCALL reads (exec_ext_call_oracle_step). `expr_body_pre`
excludes delegate raw_calls and raw_calls without revert_on_failure
(`~expr_has_evm_run`, via `expr_evm_run_root` in
lowering/supported/supportedExprTraverseScript.sml), so those cases hold
vacuously.

`stmt_state_rel` (lowering/exprLoweringPropsScript.sml) carries
`fmp_room`, the bound that puts vs_fmp above every ALLOCA allocation for
a function containing DALLOCA. The comment above the theorem says why the
statement holds.

The sibling `compile_raw_call_case` (raw_call with an explicit Bytes
data operand) is being proved separately in parallel; it is not available
here. Shared machinery you write for the CALL tail should be general
(parametric in the data pointer and length), since it serves both.

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
| Target | lowering/exprSimRawCallCalldataScript.sml | `compile_raw_call_calldata_case` (existing proof, fails since the base change; extend it). |
| Case predicates | lowering/exprSimHypsScript.sml, lowering/exprSimScript.sml | `expr_sim_case_def`, `expr_vv_case_def`, `exprs_case_def`, `expr_body_pre`, `expr_sim_inv_def`, `expr_sim_def`, `expr_vv_sim_def`, `expr_post`, `expr_exit`. |
| FMP frame | lowering/exprLoweringPropsScript.sml, lowering/intCallCalleeScript.sml | `fmp_room_def`, `stmt_state_rel_def`, `fmp_room_fields`, `fmp_room_fields_cong`, `fmp_room_exec_alloca`, `fmp_room_static_charge`, `exec_alloca_static_charge`, `stmt_state_rel_allocas_frame`, `stmt_state_rel_inst_idx`, `ci_mono_compile_msg_data_to_memory`, `run_inst_seq_fmp_room`. |
| Closest sibling (proved) | lowering/exprSimSendScript.sml | `compile_send_case`, `send_expr_sim`, `take_call_outcome_typed`: send's CALL through the oracle, same case-lemma shape. |
| Oracle call step | lowering/extCallOracleStepScript.sml | `exec_ext_call_oracle_step`, `venom_call_request_source`, `state_rel_adopt_consume` (local), `logs_rel_eq`, `local_ptrs_rel_oracle_fields`, `send_call_oracle_step`. |
| Calldata length / ALLOCA buffer pattern | lowering/exprSimCalldataSliceScript.sml (~605-636) | `context_well_typed` bound on calldata length; buffer allocation steps. |
| STATICCALL + return buffer model | lowering/exprSimHashScript.sml | `sha256_tail_run`, `sha256_tail_frame`, `hash_write_memory_disjoint`, `hash_write_memory_read_self`, `hash_returndata_state_rel`, `expr_val_rel_memory`, `expr_val_at_footprint`, `hash_alloc_mstore_frame`. |
| Operand bookkeeping | lowering/exprSimOperandsScript.sml | `expr_post_operand_kept*`, `fresh_not_local_ptr`, `alloca_clear_of_locals`. |
| JNZ / new_block control flow under frag_exec | lowering/exprSimIfExpScript.sml | how a two-block split is run. |
| Lowering defs | lowering/defs/exprLoweringScript.sml, lowering/defs/builtinSystemScript.sml, lowering/defs/contextScript.sml | `compile_call` RawCallCalldataTarget clause, `compile_ext_call_kwargs_def`, `compile_msg_data_to_memory_def`, `compile_raw_call_outbuf_def`, `compile_raw_call_finish_def`, `compile_alloc_dynamic_def`, `compile_alloc_dynamic_result`. |
| Source semantics | semantics/vyperInterpreterScript.sml | `eval_raw_call_def`, the RawCallCalldataTarget case of `eval_expr`, `eval_raw_call_preserves_non_accounts`. |
| Call context relation | lowering/defs/compileEnvScript.sml | `call_ctx_rel` (cc_calldata = txn.calldata), `local_ptrs_rel`. |
| Typing | semantics/type/vyperTypeSystemScript.sml, semantics/prop/vyperTypeInvariantsScript.sml | RawCallCalldataTarget clause of `well_typed_expr`, `raw_call_kws_ok`, `context_well_typed`. |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml, venom/defs/venomStateScript.sml, venom/defs/venomMemDefsScript.sml | DALLOCA, SETFMP, CALLDATASIZE, CALLDATACOPY, CALL/STATICCALL in oracle mode; `read_memory`, `write_memory_with_expansion`; `alloca_next_valid`. |
| Built signatures | .holbuild/ (after a build) | `.sig` files of every ancestor. |

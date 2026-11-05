# TASK: Prove the extcall/staticcall expression simulation case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (vyper-hol); the theorem is in `lowering/exprSimExtCallCaseScript.sml`

## Theorem Statement (FROZEN)

```sml
Theorem compile_extcall_case:
  !nocalls ctx func cenv cx ann is_static skip sig opts args dflt.
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       results_case nocalls ctx func cenv cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args))) /\
    (!s target t s' results t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_expr_results cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 args)) s' =
         (INL results, t') ==>
       exprs_case nocalls ctx func cenv cx
         (DROP (1 + LENGTH (FST (SND sig))) args)) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The judgments (`expr_sim_case`, `expr_vv_case`, `exprs_case`, `results_case`,
`expr_body_pre`, `expr_sim_inv`) are defined in
`lowering/exprSimHypsDefsScript.sml`; `expr_sim`, `expr_vv_sim`,
`expr_post`, `expr_exit` in `lowering/exprSimDefsScript.sml` and
`vv_post`, `vv_holds`, `storage_holds` in `lowering/loweringPostsScript.sml`.

## Completion Criteria

1. `holbuild -j4 build exprSimExtCallCaseTheory exprSimCallExtcallTheory bodySimCallExtcallTheory exprSimCallsTheory bodySimCallCasesTheory`
   passes at the default tactic timeout.
2. `holbuild check exprSimExtCallCaseTheory:compile_extcall_case`,
   `holbuild check exprSimCallExtcallTheory:extcall_expr_vv_ok` and
   `holbuild check bodySimCallExtcallTheory:extcall_body_expr_ok` show that
   the only cheat they depend on inside the theories you write is
   `vv_post_storage_live` (exprSimExtCallCase), plus admissions inherited
   from theories you do not edit (many ancestor theories are admitted in
   this tree; they are out of scope). Judge it from those checks, not from
   a build log's total CHEAT count.
3. The one allowed residual is `vv_post_storage_live`, already stated in
   `lowering/exprSimExtCallCaseScript.sml` and admitted. Do not change its
   statement or prove it. Use it wherever a storage or transient positional
   operand has to be read after the later operands. No other cheat, axiom or
   new hypothesis. In particular the returndata decoder's reject direction
   (source `evaluate_abi_decode_return` rejects => the lowered bounded memory
   decoder aborts) must be proved, in a general helper stated for the
   decoder alone, not for extcall.
4. Edit only `lowering/exprSimExtCallCaseScript.sml` and new helper theories
   you create next to it in `lowering/` (imported only by
   exprSimExtCallCase or by each other). Don't edit any other existing file.
   If an existing lemma you need is `[local]` or missing in a theory you may
   not edit, prove what you need in a helper theory (no duplicates of exported
   lemmas: reuse them).
5. No duplicate or near-duplicate lemmas. Reuse the call-frame lemmas in
   `lowering/extCallOracleStepScript.sml`. New call-frame lemmas must be
   stated for any CALL/STATICCALL with an oracle outcome, not only extcall,
   since the raw_call case will reuse them.

**If the theorem is false as stated:**
- Produce a concrete counterexample: the input, and the file:line where the
  source and the lowering diverge.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <project root>
holbuild -j4 build exprSimExtCallCaseTheory exprSimCallExtcallTheory bodySimCallExtcallTheory exprSimCallsTheory bodySimCallCasesTheory
```

## Background

This is the extcall/staticcall case of the lowering simulation's expression
induction. `extcall_expr_vv_ok` (`lowering/exprSimCallExtcallScript.sml`)
and `extcall_body_expr_ok` (`lowering/bodySimCallExtcallScript.sml`) already
follow from it. The source evaluates the target, then the positional
arguments without reading them (`eval_expr_results`), then the keyword
operands, and reads the arguments last (`eval_extcall_stages`). The
hypotheses give the operands' judgments in that order.

The lowering matches the source here:
- exact-length calldata (`ADD [enc_len; Lit 4w]`, or `Lit 4w` with no args);
- the extcodesize check and the void result keyed on `return_type = NoneT`;
- arguments laid out at their own lowered type (`MAP (lowered_value_type cenv)`);
- `expr_sim_inv` pins `cenv.ce_method_id` to the function selector;
- typing rejects `default_return_value` on a void call and requires
  assignable argument and non-void return types;
- `alloc_limits_expr` bounds the call's own buffers (`ext_call_alloc_ok` in
  `lowering/defs/allocLimitsScript.sml`), reachable through `expr_body_pre`;
- every oracle outcome's return data is shorter than 2**256
  (`outcomes_accounts_typed` in `expr_sim_inv`);
- `expr_body_pre`/`expr_sim_pre` carry
  `~supported_expr_exists call_operands_effect_root e`: no operand after the
  target has an effect (`expr_has_effect`), so the later operands don't
  change storage, and captured storage places stay live; liveness of a
  storage/transient operand pointer is `vv_post_storage_live`.

A previous attempt on an older base (before the counted gas join and static
frames; with a different, rejected vv_post change) is under
`alan-ref/seq-435/` (files renamed `*.sml.txt` so the build does not pick them up): its operand helpers (`exprSimExtCallOperandsScript.sml`,
`exprTypedOperandScript.sml`, `placeProvenanceScript.sml`,
`exprPlaceTransportScript.sml`, `exprEffectStorageScript.sml`), its partial
case proof (`exprSimExtCallScript.sml`), its returndata decode helpers
(`abiReturndataSourceScript.sml`) and its abandoned residual for the decoder reject direction. Reuse its ideas and
proofs where they port; its definitions of place provenance in `vv_post`
are not available here.

## Domain Constraints

- vyper-hol `AGENTS.md` applies: holbuild only, the 2.5 s tactic timeout
  stays, and no `TRY`/`ORELSE` around search tactics.
- The box is heavily loaded. A `tactic timed out` in a proof you did not touch
  is load, not a bug: rebuild once. If a step of yours runs near the limit,
  split it or cut its rewrite set.
- Unfolding `step_inst_base_def` whole is slow. Prefer the per-opcode step
  lemmas the lowering theories already prove.
- Source semantics, compiler definitions and the judgments are frozen. If the
  proof seems to need a definition or judgment change, stop and report it as
  a counterexample with the fix.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Theorem script | `lowering/exprSimExtCallCaseScript.sml` | statement, intuition comment, the admitted `vv_post_storage_live` |
| Judgments | `lowering/exprSimHypsDefsScript.sml`, `lowering/exprSimHypsScript.sml` | case judgments, `expr_sim_inv`, helper lemmas (`exprs_case_every_ok`, `results_case_every_ok`, `expr_vv_ok_case`) |
| Posts | `lowering/loweringPostsScript.sml`, `lowering/exprSimDefsScript.sml` | `vv_post`, `vv_holds`, `storage_holds`, `expr_post`, `expr_exit` |
| Closest proved analogue | `alan-ref/send-counted/exprSimSendScript.sml.txt` | `send` through the oracle CALL step, on the counted expr_sim (the in-tree `lowering/exprSimSendScript.sml` has its proofs admitted) |
| Oracle call step | `lowering/extCallOracleStepScript.sml` | `venom_call_request_source`, `exec_ext_call_oracle_step`, `send_call_oracle_step` |
| Lowering | `lowering/defs/exprLoweringScript.sml` | `compile_call` ExtCall arm, `compile_external_call_kwargs`, `compile_extcall_store_values`, `compile_extcodesize_check`, `compile_return_value_decode` |
| ABI encode/decode lowering | `lowering/defs/abiEncoderScript.sml`, `lowering/defs/builtinAbiScript.sml` | encoder/decoder definitions |
| Encoder proofs | `lowering/abiEncoder*Script.sml`, `lowering/abiStatic*Script.sml` | encoder correctness |
| Decoder proofs | `lowering/abiDecoder*Script.sml`, `lowering/abiBuiltinValid*Script.sml` (`lower_abi_decode_valid_source`, `compile_abi_decode_memory_valid`) | decoder success direction from any source-accepted bytes |
| Storage liveness | `lowering/accountsRelPropsScript.sml` | `storage_read_live_*`, `storage_range_agree_of_live` |
| Source semantics | `semantics/vyperInterpreterScript.sml` | `eval_ext_call`, `ext_call_precheck_ok`, default-return path, `take_call_outcome`, `adopt_call_outcome` |
| Source ABI | `semantics/vyperABIScript.sml` | `build_ext_calldata`, `evaluate_abi_decode_return` |
| Typing | `semantics/type/vyperTypeSystemScript.sml` | ExtCall case of `well_typed_expr`, `arg_type_fits` |
| State relation | `lowering/defs/compileEnvScript.sml` | `state_rel`, `request_agree` |
| Selector | `lowering/defs/selectorDispatchScript.sml` | `calldata_method_id`, `function_selector` |
| Consumers | `lowering/exprSimCallExtcallScript.sml`, `lowering/bodySimCallExtcallScript.sml`, `lowering/exprSimCallsScript.sml`, `lowering/bodySimCallCasesScript.sml` | how the case is consumed |
| Shape lemmas | `lowering/proofs/loweringShapePropsScript.sml` | `compile_external_call_kwargs_shape_under`, `compile_call_ext_shape` |
| Old attempt | `alan-ref/seq-435/` | see Background |

## Notes

- `expr_evm_run_root` covers raw_call and create only, so the extcall case is
  not vacuous in the body simulation.
- `outcomes_accounts_typed` in `expr_sim_inv` rules out the source's
  "call outcome accounts" error, as in send.
- A static frame with nonzero value: the source errors in `frame_call_value`;
  `state_rel` gives `~cc_static` and Venom's CALL aborts on static-with-value.
- The base moved under a previous alan run (its helpers in
  `lowering/abi*Script.sml` were cherry-picked here; its PLAN/STATE/LEARNINGS
  carry over). The base repair re-indexed gas to `call_result_rel_at gobs`,
  split the oracle, added revert data and the builtin-operand premise
  `(!n. bi <> Slice n) \/ ~is_extcode e`, and `expr_body_pre` now has the
  `~supported_expr_exists call_operands_effect_root e` conjunct.
  `alan-ref/send-counted/exprSimSendScript.sml.txt` is refreshed to the
  current proved `send`; re-check helpers against it before relying on them.

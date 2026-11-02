# TASK: Repair send simulation proofs after the shared compiler interfaces changed

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/exprSimSendScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem send_tail_frag:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es sa s0 t /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\
  expr_type e = NoneT ==>
  frag_exec ctx sm sb (\s. s = t)
    (\s. ?v. res = INL v /\
             expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) s)
    (expr_exit res)

Theorem send_expr_sim:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  (!arg_ty. typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
  expr_sim ctx func cenv cx ty (Call ann (Send has_gas) args dflt) es

Theorem compile_send_case:
  !nocalls ctx func cenv cx ann has_gas args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt)

Theorem compile_send_case_sim:
  !cenv ann has_gas args dflt.
    expr_sim_below cenv (expr_size (Call ann (Send has_gas) args dflt)) ==>
    expr_vv_ok cenv (Call ann (Send has_gas) args dflt)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
Every other existing theorem declaration and executable definition in the repository is frozen too. Existing proof code stays present until replaced by a checked proof.

## Completion Criteria

- Build exprSimSendTheory with the default tactic budget and kernel checking, no new admissions or axioms.
- Repair the existing proofs in lowering/exprSimSendScript.sml; preserve public theorem statements byte for byte. Do not replace failures with cheat.
- Avoid duplicate helpers; reuse existing lemmas. Any new helper is local and serves an actual proof here.
- Commit the proof changes, ending the commit message exactly with: Bot: sol (OpenAI GPT-6.1 Sol)
- If a frozen statement is false, report a checked counterexample and stop rather than altering it.

## Build

```sh
holbuild --max-heap 4000 -j2 build exprSimSendTheory
```

## Background

This branch integrates creation builtins with the shared compiler context and pending-deletion state. The send theory still uses proofs from the older interfaces. A mechanical correction added the leading ctx argument to the local send_call_read_step declaration; its caller already supplies that context. The default build now reaches send_tail_frag and fails at a source frame-preservation step. Later existing proof consumers must also build.

The declared send_tail_frag statement has parsed in owner build16134. Ancestors built or restored successfully. Do not change compiler/source behavior, theorem premises, outcomes, request consumption, storage relations or fixture coverage.

## Domain Constraints

- HOL4 proofs only. No executable definition changes, axioms, cheats, oracle facts, stronger hypotheses or theorem deletion.
- Keep the default tactic timeout. No TRY or ORELSE around proof search, no timeout bypasses.
- Modify only lowering/exprSimSendScript.sml for this task. Do not edit unrelated files or other branches, and do not push.
- Existing admissions elsewhere are permitted dependencies; no new admissions.
- This task file is preparation material, not a requested code deliverable.

## Available Resources

- lowering/exprSimSendScript.sml: existing send proofs and frozen statements.
- lowering/exprLoweringPropsScript.sml: stmt_state_rel and frame transport lemmas.
- lowering/exprSimHypsScript.sml: simulation invariants and result interfaces.
- lowering/extCallOracleStepScript.sml: send_call_oracle_step.
- lowering/exprSimOperandsScript.sml: argument and callback interfaces.
- lowering/stmtSimReasonScript.sml: surrounding fragment interfaces.
- semantics/vyperStateScript.sml and semantics/vyperInterpreterScript.sml: source state and interpreter (locate definitions if files use a different subdivision).
- extCallOracleScript.sml and semantics/vyperCallOutcomeScript.sml: oracle outcomes and adoption.
- docs/HOL4_PROOF_CONTROL_LESSONS.md: repository proof control guidance.

## Notes

Owner build failed in send_tail_frag while establishing es'.scopes = es1.scopes and es'.immutables = es1.immutables. Preserve the original public theorem preconditions and result. Independent statement validity check is recorded before launch.

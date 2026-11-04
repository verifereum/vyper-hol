# TASK: Preserve the full expression frame at the fixed explicit GAS leaf

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering

## Theorem Statement (FROZEN)
```sml
Theorem msg_gas_typed[local]:
  expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es ==>
  ann = env_item_type MsgGas /\ args = []

Theorem msg_gas_state_frame:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs)
    (s with <|vs_gas_readings := readings; vs_inst_idx := k|>)

Theorem msg_gas_post_frame[local]:
  compile_env_var MsgGas sa = (Var out,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 ==>
  expr_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s0 (es with gas_obs := []) (IntV (&w2n w)) (Var out)
    (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>))

Theorem compile_msg_gas_post:
  !ctx func cenv cx env ty ann args es sa sb op s0.
    expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es /\
    lower_value compile_expr cenv ty (Builtin ann (Env MsgGas) args) sa =
      (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_summary_at (ctx, func) [T]
      (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx))
      (es, s0)
      (\res ee t.
         (?v. res = INL v /\
              expr_post ctx func cenv cx (Builtin ann (Env MsgGas) args)
                es sa sb s0 ee v op t) /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. F)
```
Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria
- Prove the complete compile_msg_gas_post and its existing helpers without admissions or definition/statement changes.
- Build msgGasPostTheory at the default step limit, preserving fixed [T], the complete expr_post, exact landing, actual memory-safe path and arbitrary unused source tails.
- Search for and reuse existing helpers rather than adding duplicate lemmas, including local copies.

## Build
holbuild -j4 build msgGasPostTheory

## Background
The compiled explicit read already has a checked same-fuel memory-safe counted path, including exhausted target streams. This theorem couples that actual path to the real source action and the complete expression frame. The strict summary requires both execution and its postcondition unconditionally. It is an additive producer for the shared migration, not a substitute for that migration.

## Domain Constraints
Only lowering/msgGasPostScript.sml and prover task state may change. Keep all frozen statements and executable/proof-facing definitions unchanged. Preserve existing proofs; do not replace them with placeholders. No new premise, feature restriction, admission, axiom, timeout override or TRY/ORELSE around search. Consumed proof helpers are allowed after searching for existing ones; export reusable helpers. Do not alter the source or target oracle semantics.

## Available Resources
- lowering/msgGasPostScript.sml
- lowering/msgGasSimScript.sml
- lowering/gasSummaryScript.sml
- lowering/fragGasPathMemScript.sml
- lowering/exprSimScript.sml
- lowering/exprSimHypsScript.sml
- lowering/exprLoweringPropsScript.sml
- lowering/defs/exprLoweringScript.sml
- lowering/defs/compileEnvScript.sml
- semantics/vyperInterpreterScript.sml
- semantics/vyperStateScript.sml
- venom/proofs/gasCountScript.sml

## Notes
The exact current root has not yet been reached by the owner check: untouched prerequisites have required their single unchanged retries. Owner46135 stopped before this root at untouched abiEncoderVarTransport.abi_encoder_step_inputs_defined line105; its single unchanged retry is pending. The current root has not yet parsed in this tree. Existing hand proofs stay intact. Independent whole-statement audit /root/audit_msg_gas_full_post returned PROVABLE on2026-11-04 at exact script SHA2567b3180a51b134648e53f1b23f37b280d1d6f9308495776b1135ca21e3dfeb105; all four complete schemas checked. This is logical audit, not kernel verification. Do not start concurrently with another owner build or proof job in this worktree.

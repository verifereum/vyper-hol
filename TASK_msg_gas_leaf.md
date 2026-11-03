# TASK: Prove the concrete explicit msg.gas leaf against actual counted execution

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem compile_msg_gas_path:
  compile_env_var MsgGas sa = (op, sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out w.
    op = Var out /\ gas_prefix 1 s0.vs_gas_readings = [w] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_path ctx func s0 1
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>)))

Theorem compile_msg_gas_summary:
  compile_env_var MsgGas sa = (op, sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary (ctx, func)
    (bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
          (read_result cx)) (es, s0)
    (\res es_end t.
       ?w. res = INL (IntV (&w2n w)) /\
           es_end = (es with gas_obs := []) /\
           eval_operand op t = SOME w /\
           t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           t.vs_gas_readings = DROP 1 s0.vs_gas_readings)
    (\res es_end r. F)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
All existing definitions are frozen too.

## Completion Criteria

- Prove both frozen roots without new admissions.
- Build msgGasSimTheory at the default tactic limit.
- Prove against actual GAS execution and the strict unconditional source/path/post summary. Do not use the admitted compile_msg_gas_sim or an assumption of its conclusion.
- Additional helper lemmas may be introduced in this new script; no helper definitions or changes to existing scripts without owner review.

## Build

```sh
holbuild -j2 build msgGasSimTheory
```

## Background

Source msg.gas consumes only its explicit source event. The compiler emits one GAS instruction, which consumes one target event even when its oracle is exhausted and returns zero. The target path must start at the actual compiler entry and land at the actual compiler endpoint. These concrete leaf results feed the pending shared judgment migration; the existing expr_sim statement is false under its old gas relation and is outside this task. The new strict summary requires all source/path/post obligations unconditionally.

## Domain Constraints

- Edit only lowering/msgGasSimScript.sml, preserving both frozen statements.
- Preserve compiler and source semantics, shared lowering judgments, all stage contracts and existing proof statements.
- No new cheats, axioms, or oracle theorems; remove the two new task placeholders.
- No opcode-absence or no-GAS shortcut. Counts follow actual execution, not continuation compatibility or list-length differences.
- No tactic-timeout overrides or TRY/ORELSE/FIRST around search; select goals explicitly.
- Existing admitted ancestors are dependencies only; do not call an admitted generic lowering theorem to obtain the task's leaf claim.
- Do not rely on generated variable names. Use normal Theory/Ancestors headers and Theorem/Proof/QED syntax.

## Available Resources

- `lowering/msgGasSimScript.sml`
- `lowering/gasSummaryScript.sml`
- `lowering/fragGasPathScript.sml`
- `venom/proofs/gasCountScript.sml`
- `venom/proofs/gasOracleReplayScript.sml`
- `lowering/fragExecScript.sml`
- `lowering/defs/exprLoweringScript.sml`
- `lowering/defs/emitHelperScript.sml`
- `lowering/defs/compileEnvScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`
- `venom/defs/venomStateScript.sml`
- `semantics/vyperInterpreterScript.sml`
- `semantics/type/vyperTypeSystemScript.sml`

## Notes

The parser/prerequisite build passed (msgGasSimTheory, 1011.648s including machine-memory waits): both exact task placeholders were saved and exported, with no new-script parser warning. An independent audit found both exact schemas PROVABLE, including empty target readings and full source builtin type bounds. Owner forced replay and kernel-tag checks follow the returned proof. No shared judgment, source-semantic or stage-interface change is authorized in this task.

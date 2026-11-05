# TASK: Prove the concat lowering simulation case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimConcatScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_concat_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Concat n) args)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- `holbuild -j4 build exprSimConcatTheory` passes at the default step limit with no CHEAT in exprSimConcatTheory; compile_concat_case is proved, for nocalls = T and F, without moving its admission to a helper.
- No new admissions, axioms, definition changes, statement changes of existing theorems, or timeout overrides.
- Helper lemmas go in lowering/exprSimConcatScript.sml or in new leaf theories next to it named exprSimConcat<Part> (e.g. exprSimConcatLoop). Do not edit any other existing file. If a fact you need belongs in an existing shared theory, prove it in a new exprSimConcat<Part> leaf and say so in your report.
- If the frozen statement is false, report a concrete counterexample and stop; do not amend definitions or assumptions.
- Commit with trailer `Bot: opus (Claude Opus 5.5)`. Do not push.

## Build

```sh
holbuild -j4 build exprSimConcatTheory
```

From this project root. Keep the default 2.5-second per-step tactic timeout. Do not build CI roots, the dependent cone, EEST or evalCompilerBytecodeParityTheory.

## Background

Case lemma of the expression simulation (compile_expr_sim in lowering/exprSimMainScript.sml), re-exported by lowering/exprSimBuiltinsScript.sml. From the operand judgments (exprs_case: each operand's counted expr_sim_case/expr_vv_case, later operands conditional on earlier ones evaluating) derive the raw-value simulation of `concat(...)`: the source evaluates every operand, then evaluate_concat; the lowering allocates a result buffer (concat_alloc_size) and a 64-byte offset temporary, then per operand lowers it (lower_value) and copies its bytes (MCOPY for Bytes/String, a full-word MSTORE for bytesM) at the running offset, and finally writes the length word. The judgments are counted (GAS join): see gas_outcome and gas_marked_path.

Several ancestor theories are built here with their proofs admitted (a scratch overlay commit at the base of this branch); treat their statements as given and do not edit them.

## Domain Constraints

- holbuild only: no Holmake, hol4-mcp, holbuild run/repl, interactive g()/e(), or --skip-goalfrag.
- Never wrap metis or other search in TRY/ORELSE; select goals with >~, >-, >|.
- No fixture changes, holproject.toml changes, or executable-definition edits (lowering/defs, venom/defs, semantics, frontend).
- Do not use auto-generated hypothesis names; use rename1/qpat_x_assum.

## Available Resources

| Resource | Location |
|---|---|
| Assigned theorem | lowering/exprSimConcatScript.sml |
| Source side, already proved (use it): typed operands are BytesV/StringV lists and evaluate_concat returns their FLAT | lowering/exprSimConcatSourceScript.sml (evaluate_concat_typed_bytes, evaluate_concat_typed_string) |
| Operand-list induction under the counted judgments (closest template for the operand loop: suspend head_normal/head_exit/head_exempt, wb_args_head_exempt_cert, gas_marked_exec_bind_normal) | lowering/exprSimWordArgsScript.sml (lower_word_args_sim, compile_word_builtin_sim) |
| Straight-line code as a counted path with 0 GAS reads | lowering/fragGasSeqScript.sml (tuple_run_inst_seq_gas_path) |
| Case judgments (expr_vv_case, exprs_case, expr_body_pre, expr_sim_inv) | lowering/exprSimHypsDefsScript.sml |
| Counted judgments expr_sim / expr_vv_sim, expr_exit | lowering/exprSimDefsScript.sml |
| vv_post, vv_holds, expr_post, frame clauses, val_footprint | lowering/loweringPostsScript.sml |
| gas_outcome and its composition lemmas | lowering/gasOutcomeScript.sml |
| gas_marked_path, counted path composition | lowering/fragGasModeScript.sml, fragGasPathScript.sml, fragGasPathMemScript.sml, fragGasSeqScript.sml, fragGasSeqMemScript.sml, fragGasSeqAbortScript.sml |
| Operand/typing lemmas used by the case proofs | lowering/exprSimHypsScript.sml |
| Concat step memory facts (fixed and bytes steps) | lowering/concatMemoryScript.sml |
| Other builtin cases proved with these judgments (closest patterns) | lowering/exprSimBuiltinsScript.sml, exprSimWordBuiltinsScript.sml, exprSimWordArgsScript.sml, exprSimHashScript.sml, exprSimUint2StrScript.sml, exprSimLiteralBufferScript.sml, exprSimBufferScript.sml, exprSimBufferStoreScript.sml, exprSimAllocScript.sml |
| Interleaved operand evaluation + stores into a fresh buffer (MakeArray/tuple) | lowering/exprSimAggregateLoopsScript.sml, exprSimAggregatesScript.sml, exprSimTupleScript.sml |
| Memory reading/value layout of bytestrings | lowering/exprSimMemoryReadScript.sml, exprSimMemoryValuesScript.sml, builtinBytesMemoryScript.sml, typedMemoryCopyScript.sml |
| Compile-state freshness, ci_mono, reservations | lowering/exprLoweringPropsScript.sml, exprOperandVarScript.sml, instMemFrontierScript.sml |
| Concat lowering: compile_concat, concat_alloc_size, concat_data_bound, concat_payload_capacity, Concat branch of compile_builtin_dispatch_body | lowering/defs/exprLoweringScript.sml |
| alloc_limits_expr (Concat clause bounds concat_alloc_size) | lowering/defs/allocLimitsScript.sml |
| Source: evaluate_concat, evaluate_concat_loop, init_concat_output | semantics/vyperValueOperationScript.sml |
| Source builtin dispatch (evaluate_builtin Concat) | semantics/vyperContextScript.sml |
| eval_expr Builtin case | semantics/vyperInterpreterScript.sml |
| Typing: well_typed_builtin_app Concat (SUM bytelike_type_bound <= n), bytelike_type_bound | semantics/type/vyperTypeSystemScript.sml |
| Builtin value typing / concat success lemmas | semantics/prop/vyperTypeBuiltinsScript.sml |
| Eval type soundness (evaluated values are well typed) | semantics/prop/vyperTypeEvalSoundnessScript.sml |
| Proof-control lessons | docs/HOL4_PROOF_CONTROL_LESSONS.md |

## Notes

Keep alan working files out of the proof commits' theory files.

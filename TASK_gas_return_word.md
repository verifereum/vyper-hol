# TASK: Prove counted simulation for an internal word return

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimReturnWordScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_return_word_int_frag:
  !ctx func cx lctx cenv ty e es rpc rsz ret_tv.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
    expr_type e = ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ret_tv /\
    expr_sim ctx func cenv cx ty e es /\
    (!sa op sb. lower_value compile_expr cenv ty e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx ty (Return (SOME e)))
      (eval_stmt cx (Return (SOME e))) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimReturnWordTheory` passes with the assigned root.
2. No new admissions, axioms, proof-parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. All definitions and other existing theorem statements remain unchanged. Reuse existing facts; export or move matching local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build stmtSimReturnWordTheory
```

## Background

The shared statement judgment now simulates the actual source action under selected explicit gas readings. The word-return root has been mechanically restated to pass eval_stmt as the source action, removing its obsolete fixed result/state arguments and evaluation premise. All other hypotheses are retained. Its old proof remains. Shared pure return facts stay in stmtSimReturn; the independent tuple root is outside this task.

## Domain Constraints

Independent audit answered PROVABLE for this exact actual-source word root, including ordinary exits and the existing concrete exemption certificates. Preserve universal source admissibility before witness choice, every unused source tail, actual counted target execution, the complete return postcondition and return-PC/state frames. Keep the existing strict summary and concrete certificate constructors. No new source-equivalence certificate, theorem premise, evaluator, opcode restriction or exception exemption. Do not modify or attempt the independent tuple root.

## Available Resources

- lowering/stmtSimReturnWordScript.sml: assigned exact root and retained proof.
- lowering/stmtSimReturnScript.sml: existing pure return facts and intret_q_gas_obs.
- lowering/stmtSimDefsScript.sml, lowering/stmtSimPropsScript.sml, lowering/loweringPostsScript.sml: actual statement judgment and full posts.
- lowering/exprSimDefsScript.sml, lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/gasSummaryComposeScript.sml: counted expression/source-action boundaries.
- lowering/gasExemptCertScript.sml, lowering/gasIntCallBodyScript.sml, lowering/gasIntCallArgsScript.sml: existing concrete certificate transport.
- lowering/fragGasPathScript.sml, venom/proofs/gasCountScript.sml: actual target paths and GAS counts.
- lowering/exprLoweringPropsScript.sml, lowering/emitHelperPropsScript.sml: compiler and execution facts.
- lowering/defs/stmtLoweringScript.sml, lowering/defs/compileEnvScript.sml: actual return compiler and result/state relations.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source actions and monad laws.

## Notes

The parser owner checks the shared pure owner and the mechanically restated root. If a prerequisite stops it before the root, the statement has not yet been parsed; the independent exact statement audit is the launch prerequisite. No proof strategy is prescribed. Existing source/target executable definitions, gas judgments, strict posts and error gates are frozen.

# TASK: Prove counted simulation for an internal tuple return

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimReturnTupleScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_return_tuple_int_frag:
  !ctx func cx lctx cenv e es rpc rsz tys ret_tv.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = LENGTH tys /\ 1 < LENGTH tys /\
    cenv.ce_return_buf = NONE /\
    expr_type e = TupleT tys /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME ret_tv /\
    (!gs v es1. (do raw <- eval_expr cx e; read_result cx raw od)
                 (es with gas_obs := gs) =
               (INL v, es1) ==> value_has_type ret_tv v) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    (!sa op sb. local_ptrs_reserved cenv sa /\
                lower_value compile_expr cenv (TupleT tys) e sa = (op, sb) ==>
                !x. op = Var x ==> not_fresh_at sb x) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx (TupleT tys) (Return (SOME e)))
      (eval_stmt cx (Return (SOME e))) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimReturnTupleTheory` passes with the assigned root.
2. No new admissions, axioms, proof-parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. All definitions and other existing theorem statements remain unchanged. Reuse existing facts; export or move matching local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build stmtSimReturnTupleTheory
```

## Background

The shared statement judgment now simulates the actual source action under selected explicit gas readings. The tuple-return root passes eval_stmt as the actual source action, removing obsolete fixed result/state arguments and evaluation premise. Its value-typing premise now covers every source gas oracle, as required for selected explicit readings. This internal premise change is approved: the actual body producer supplies it from expr_body_pre_gas_obs and source type soundness. All other hypotheses and the old proof are retained. Shared pure return facts stay in stmtSimReturn; the independent word root is outside this task.

## Domain Constraints

Independent audit answered PROVABLE for this exact actual-source tuple root, including ordinary exits and the existing concrete exemption certificates. Preserve universal source admissibility before witness choice, every unused source tail, actual counted target execution, the complete return postcondition and return-PC/state frames. Keep the existing strict summary and concrete certificate constructors. No new source-equivalence certificate, theorem premise, evaluator, opcode restriction or exception exemption. Do not modify or attempt the independent word root.

## Available Resources

- lowering/stmtSimReturnTupleScript.sml: assigned exact root and retained proof.
- lowering/stmtSimReturnScript.sml: existing pure return facts and intret_q_gas_obs.
- lowering/stmtSimDefsScript.sml, lowering/stmtSimPropsScript.sml, lowering/loweringPostsScript.sml: actual statement judgment and full posts.
- lowering/exprSimDefsScript.sml, lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/gasSummaryComposeScript.sml: counted expression/source-action boundaries.
- lowering/gasExemptCertScript.sml, lowering/gasIntCallBodyScript.sml, lowering/gasIntCallArgsScript.sml: existing concrete certificate transport.
- lowering/fragGasPathScript.sml, venom/proofs/gasCountScript.sml: actual target paths and GAS counts.
- lowering/exprLoweringPropsScript.sml, lowering/emitHelperPropsScript.sml: compiler and execution facts.
- lowering/defs/stmtLoweringScript.sml, lowering/defs/compileEnvScript.sml: actual return compiler and result/state relations.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source actions and monad laws.

## Notes

The shared pure owner built. The approved restated root parsed in the owner build, then its retained old proof failed at the expected statement-wrapper mismatch. Independent exact statement audit is complete. No proof strategy is prescribed. Existing source/target executable definitions, gas judgments, strict posts and error gates are frozen.

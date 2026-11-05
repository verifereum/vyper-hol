# TASK: Prove word-local Assign against its consuming gas source action

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem assign_local_stmt_frag_given_unforce[local]:
  !ctx func cx lctx RetQ cenv ty id e es p sz vtyp etv.
    (!memory tops ctx' func' cx' e' es' s0 marks err ee leaf finish.
       gas_exempt_cert memory tops (ctx', func')
         (ignore_bind (bind (eval_expr cx' e') (read_result cx')) (return ()))
         (es', s0) marks (err, ee) (leaf, finish) ==>
       gas_exempt_cert memory tops (ctx', func')
         (ignore_bind (eval_expr cx' e') (return ()))
         (es', s0) marks (err, ee) (leaf, finish)) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       store_lays_out etv entry.type v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/stmtSimAssignScript.sml` with its old proof body, which
targets the obsolete fixed-result interface. All existing definitions and
other theorem statements are frozen. New proof-only helper lemmas are weakly
frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `stmtSimAssignTheory` builds normally (proof steps on, default step
   limit) with no CHEAT and no parser warnings.
3. Reuse existing helpers rather than duplicating them; put reusable
   helpers in the theory where they belong, outside `lowering/defs`.

## Build

```sh
holbuild -j4 build stmtSimAssignTheory
```

## Background

The statement relates the complete source action of `x = e` (x a local
word variable, e a word expression) to counted target execution of its
lowering (e's code, unwrap, one MSTORE at x's pointer). The target is
`stmt_frag` in `lowering/stmtSimDefsScript.sml` (`stmt_framed_frag`):
under `gas_admissible` for the statement's action it must give a
`gas_outcome` (`lowering/gasOutcomeScript.sml`): either a
`gas_summary_at` with the full `stmt_post`/`stmt_exit`, or an exemption
certificate (`gas_exempt_cert`, `lowering/gasExemptCertScript.sml`) for the
statement's own action.

The source `Assign` (`semantics/vyperInterpreterScript.sml`, `evaluate_def`
Assign case) evaluates e, then the target place (a scope lookup for x),
then forces e's result with `read_result`, then `write_place`. So it is not
literally `bind (bind (eval_expr cx e) (read_result cx)) k`; the place step
sits between `eval_expr` and `read_result`. `expr_sim` hands back counted
facts for the forced expression action
`bind (eval_expr cx e) (read_result cx)`.

The first hypothesis of the frozen statement is exactly the new
certificate rule `gas_exempt_cert_unforce_result` (approved, being added to
`gasExemptCert` separately): it turns an exemption certificate of the forced
expression into one of the raw `eval_expr`. Use it as a hypothesis; do not
add or prove the rule itself. The existing rule
`gas_exempt_cert_error_result` lifts a raw `eval_expr` certificate to a
bind on it.

`assign_local_word_success_run` and the old proof body use the obsolete
fixed-result `frag_exec` interface and no longer build. Remove or replace
them with counted versions; do not restore fixed-reading conclusions.

## Domain Constraints

- No executable definition changes, added assumptions, admissions,
  timeout overrides, or search tactics wrapped in `TRY`/`ORELSE`.
- Keep every full post, frame and storage agreement. Use actual counted
  GAS paths and all source gas tails; do not infer counted paths from
  legacy `frag_exec`, discard exempt certificates, or restrict GAS.
- Do not restore or strengthen the old `expr_sim_error_run`.
- Keep `is_word_type_no_length_word`, `eval_assign_local`,
  `eval_assign_local_error` and `assign_local_word_code_parts` unchanged
  (other theories use them).
- Other theories (`stmtSimAssignMem`, `stmtSimAssignAttr`,
  `bodySimStmtCases`) are outside this task.

## Available Resources

- Target: `lowering/stmtSimAssignScript.sml`
- Statement action and posts: `lowering/stmtSimDefsScript.sml`
- Expression action and `expr_sim`/`expr_post`: `lowering/exprSimDefsScript.sml`
- Counted outcomes: `lowering/gasOutcomeScript.sml`
- Summaries and composition: `lowering/gasSummaryScript.sml`, `lowering/gasSummaryComposeScript.sml`
- Exemption certificates: `lowering/gasExemptCertScript.sml`
- Forced-expression-then-gas-free-continuation combinator:
  `lowering/stmtSimForcedScript.sml` (`forced_then_summary`,
  `forced_then_outcome`, `forced_then_admissible`, `forced_then_stmt_outcome`)
- Worked port of the analogous declaration `x: T = e` (forced RHS then a
  store), proved against the same interface:
  `lowering/stmtSimDeclScript.sml` (`compile_annassign_stmt_frag`) and its
  helpers `lowering/stmtSimDeclSourceScript.sml`,
  `lowering/stmtSimDeclGasScript.sml`, `lowering/stmtSimDeclPathScript.sml`
  (`emit_inst_zero_marked_path`, `emit_mstore_marked_path`),
  `lowering/stmtSimDeclComposeScript.sml`
- Store into a local: `lowering/stmtSimAssignStoreScript.sml`
  (`assign_local_store_run`), `lowering/stmtSimDeclStoreScript.sml`
- Counted sequencing: `lowering/fragGasSeqScript.sml`
- Source interpreter: `semantics/vyperInterpreterScript.sml`

## Notes

The statement is the restatement of `compile_assign_local_stmt_frag` from
the fixed-result form (`es res es'` plus an `eval_stmt` premise) to the
action form, plus the certificate-rule hypothesis. The layout premise
quantifies over every gas list `gs` (approved pattern from the declaration
port); its producer is gas-observation invariant. Once the rule lands, the
public `compile_assign_local_stmt_frag` is derived from this lemma outside
this task.

The statement has not been parsed by a build yet: the theory currently
stops earlier, at the obsolete `assign_local_word_success_run`.
Ancestors of `stmtSimAssignTheory` build on this tree.

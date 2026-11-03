# TASK: Preserve reason-expression exits for code-pointer reasons

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem unwrap_code_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x w. not_fresh_at sa x /\ lookup_var x sbase = SOME w ==>
                  lookup_var x s = SOME w)) R
```

```sml
Theorem unwrap_code_reason_var:
  !cenv ty p sa op sb.
    reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) ==>
    ?x. op = Var x
```

```sml
Theorem compile_revert_code_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = sbase) (\s. F) R
```

```sml
Theorem compile_raise_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    ~cenv.ce_is_ctor /\
    eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r))) es res es'
```

```sml
Theorem compile_assert_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    ~cenv.ce_is_ctor /\
    eval_stmt cx (Assert e (AssertReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r))) es res es'
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
Every existing theorem header is saved in `.agent-files/seq240/reason-code-frozen-headers.json`.

## Completion Criteria

1. `stmtSimReasonCodeTheory` builds with all its existing declarations proved and no admissions.
2. All public statements and executable definitions remain byte-identical.
3. Only the allowed proof file is changed; no new admissions, proof-search exception wrappers, or timeout changes.

## Build

`holbuild --max-heap 8000 -j2 build stmtSimReasonCodeTheory`

## Background

The code-pointer reason proof fails in `compile_raise_code_reason_frag` after its source reason can Halt. Its local revert helper currently asks for an unconditional revert exit, while the source raises a reason only after the reason returns a value. Other reason forms already retain that distinction. The unchanged public raise/assert statements were independently audited PROVABLE.

## Domain Constraints

- Modify ONLY `lowering/stmtSimReasonCodeScript.sml`.
- All public declarations and all existing executable definitions are frozen.
- All other existing local theorem statements are frozen, except the two exact permitted weakenings below. Their proofs may change.
- In `reason_code_expr_revert_frag[local]`, replace only the premise `(!t. R (Abort Revert_abort t))` with `(!tv t. res1 = INL tv ==> R (Abort Revert_abort t))`. Here res1 is the raw evaluator result.
- In `reason_code_expr_revert_forced_frag[local]`, replace the same premise with the same conditional form. Here res1 is the forced/read result.
- These are pre-audited local weakenings, not permission to add any hypothesis or change any stage/public statement.
- Keep existing proof code until replaced by a checked proof. No temporary cheat.
- New consumed helpers may be added only as `[local]` and only when the concrete proof needs them. Do not add definitions.
- Never wrap search in TRY/ORELSE; never raise or disable the default tactic timeout. Use the shared holbuild wrapper, default resources, at most -j2.
- No interactive HOL workflow; no Holmake; do not edit `.alan` state or task scaffolding.
- Commits end with `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/stmtSimReasonCodeScript.sml`: failing code-pointer reason proof, all public goals.
- `lowering/stmtSimReasonExprScript.sml`: reason_expr_revert_frag, reason_expr_revert_frag_general, raise_reason_exits, compile_raise_reason_frag.
- `lowering/exprSimScript.sml`: vv_post, vv_holds and immutable_holds; successful target code-pointer observations.
- `lowering/fragExecScript.sml`: fragment composition and exit-prefix infrastructure (locate the exact existing file if this spelling differs).
- `lowering/defs/exprLoweringScript.sml`: expression compilation definitions.
- `semantics/vyperInterpreterScript.sml`: Raise/Assert source evaluator.

## Notes

Owner diagnosis18284 reached the unchanged public theorem and failed `goal_assum (drule_at (Pat compile_expr...))` because the first obligation is still an unconditional revert-exit conjunct. All preceding ten lemmas built. Their statements are parsed. No compiler or source-definition change is requested. Independently audited raw/forced conditional variants are PROVABLE; all public goals remain frozen.
